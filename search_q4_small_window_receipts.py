#!/usr/bin/env python3
"""
Run the q = 4 maximal-control exact-upgrade search on the remaining small window
8 <= n <= 13, keeping structured receipts for every pass.

Each pass uses a fixed per-host-shape timeout. Later passes rerun only the host
shapes that were still "unknown" in the previous receipt.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent
SEARCH_SCRIPT = REPO_ROOT / "search_q4_maximal_control_host_upgrade.py"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="directory where pass receipts, logs, and the manifest will be written",
    )
    parser.add_argument(
        "--start-n",
        type=int,
        default=8,
        help="smallest graph order to test (default: 8)",
    )
    parser.add_argument(
        "--end-n",
        type=int,
        default=13,
        help="largest graph order to test (default: 13)",
    )
    parser.add_argument(
        "--pass-timeout-ms",
        type=int,
        nargs="+",
        default=[60000, 600000],
        help="per-shape timeouts for successive passes (default: 60000 600000)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="how many n-values to run in parallel inside each pass (default: 1)",
    )
    return parser.parse_args()


def ensure_valid_args(args: argparse.Namespace) -> None:
    if args.start_n < 7:
        raise SystemExit("--start-n must be at least 7")
    if args.end_n < args.start_n:
        raise SystemExit("--end-n must be at least --start-n")
    if args.jobs < 1:
        raise SystemExit("--jobs must be positive")
    if any(timeout <= 0 for timeout in args.pass_timeout_ms):
        raise SystemExit("all --pass-timeout-ms values must be positive")


def load_receipt(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def unknown_shapes_from_receipt(path: Path) -> list[tuple[int, ...]]:
    data = load_receipt(path)
    return [
        tuple(int(v) for v in item["host_extra"])
        for item in data["shape_results"]
        if item["status"] == "unknown"
    ]


def summarize_receipt(path: Path) -> dict[str, Any]:
    data = load_receipt(path)
    counts = {"sat": 0, "unsat": 0, "unknown": 0}
    for item in data["shape_results"]:
        counts[item["status"]] += 1
    return {
        "receipt_path": str(path),
        "final_status": data["final_status"],
        "host_shapes_requested_count": data["host_shapes_requested_count"],
        "forbidden_exact_witnesses": data["forbidden_exact_witnesses"],
        "counts": counts,
    }


def shapes_for_next_pass(previous_receipt: Path | None) -> list[tuple[int, ...]] | None:
    if previous_receipt is None or not previous_receipt.exists():
        return None
    data = load_receipt(previous_receipt)
    if data["final_status"] in {"sat", "unsat"}:
        return []
    return unknown_shapes_from_receipt(previous_receipt)


def run_case(
    *,
    n: int,
    timeout_ms: int,
    pass_dir: Path,
    shapes: list[tuple[int, ...]] | None,
) -> dict[str, Any]:
    receipt_path = pass_dir / f"n{n}.json"
    stdout_path = pass_dir / f"n{n}.stdout.log"
    stderr_path = pass_dir / f"n{n}.stderr.log"

    if shapes == []:
        return {
            "n": n,
            "status": "skipped",
            "reason": "previous pass already resolved this n",
            "receipt_path": None,
        }

    command = [
        sys.executable,
        str(SEARCH_SCRIPT),
        "--n",
        str(n),
        "--timeout-ms",
        str(timeout_ms),
        "--receipt-path",
        str(receipt_path),
    ]
    if shapes is not None:
        for shape in shapes:
            command.extend(["--host-extra", ",".join(str(v) for v in shape)])

    pass_dir.mkdir(parents=True, exist_ok=True)
    with stdout_path.open("w", encoding="utf-8") as stdout, stderr_path.open(
        "w", encoding="utf-8"
    ) as stderr:
        completed = subprocess.run(
            command,
            cwd=REPO_ROOT,
            stdout=stdout,
            stderr=stderr,
            text=True,
            check=False,
        )

    if completed.returncode != 0:
        return {
            "n": n,
            "status": "error",
            "returncode": completed.returncode,
            "receipt_path": str(receipt_path) if receipt_path.exists() else None,
            "stdout_path": str(stdout_path),
            "stderr_path": str(stderr_path),
        }

    summary = summarize_receipt(receipt_path)
    summary.update(
        {
            "n": n,
            "status": "ok",
            "timeout_ms": timeout_ms,
            "stdout_path": str(stdout_path),
            "stderr_path": str(stderr_path),
            "requested_unknown_only": shapes is not None,
            "requested_shape_count": None if shapes is None else len(shapes),
        }
    )
    return summary


def write_manifest(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    args = parse_args()
    ensure_valid_args(args)

    manifest_path = args.output_dir / "manifest.json"
    cases: dict[str, dict[str, Any]] = {
        str(n): {"passes": [], "final_status": "pending"} for n in range(args.start_n, args.end_n + 1)
    }

    for pass_index, timeout_ms in enumerate(args.pass_timeout_ms, start=1):
        pass_dir = args.output_dir / f"pass{pass_index:02d}-{timeout_ms}ms"
        tasks: list[tuple[int, list[tuple[int, ...]] | None]] = []

        for n in range(args.start_n, args.end_n + 1):
            case = cases[str(n)]
            previous_receipt = None
            for prior in reversed(case["passes"]):
                if prior.get("status") == "ok" and prior.get("receipt_path") is not None:
                    previous_receipt = Path(prior["receipt_path"])
                    break
            shapes = shapes_for_next_pass(previous_receipt)
            tasks.append((n, shapes))

        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = {
                executor.submit(
                    run_case, n=n, timeout_ms=timeout_ms, pass_dir=pass_dir, shapes=shapes
                ): n
                for n, shapes in tasks
            }
            for future in as_completed(futures):
                result = future.result()
                n = result["n"]
                cases[str(n)]["passes"].append(result)
                if result["status"] == "ok":
                    cases[str(n)]["final_status"] = result["final_status"]
                elif result["status"] == "error":
                    cases[str(n)]["final_status"] = "error"

        write_manifest(
            manifest_path,
            {
                "script": str(Path(__file__).name),
                "search_script": str(SEARCH_SCRIPT.name),
                "n_range": [args.start_n, args.end_n],
                "pass_timeouts_ms": args.pass_timeout_ms,
                "jobs": args.jobs,
                "cases": cases,
            },
        )

        print(f"completed pass {pass_index} (timeout {timeout_ms} ms)")
        for n in range(args.start_n, args.end_n + 1):
            case = cases[str(n)]
            latest = case["passes"][-1]
            if latest["status"] == "ok":
                counts = latest["counts"]
                print(
                    f"  n={n}: {latest['final_status']} "
                    f"(sat={counts['sat']}, unsat={counts['unsat']}, unknown={counts['unknown']})"
                )
            elif latest["status"] == "skipped":
                print(f"  n={n}: skipped")
            else:
                print(f"  n={n}: error")

    print(f"manifest written to {manifest_path}")


if __name__ == "__main__":
    main()
