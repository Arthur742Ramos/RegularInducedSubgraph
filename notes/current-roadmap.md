# Current roadmap

This note records the shortest credible path from the current modular-control formalization to the
remaining open work.

## Where the formalization stands

The current reduction chain has already moved the main asymptotic bottleneck through the following
equivalent or downstream targets:

1. fixed-witness terminal regularization;
2. one-control host terminal regularization;
3. bounded-host terminal regularization;
4. single-control host terminal regularization;
5. exact-card single-control host terminal regularization.

On the finite side, the key positive bridge is now already in place:

- `hasControlBlockModularCascadeFrom_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees`,
- together with its witness-level wrappers in `RegularInducedSubgraph/Modular/Cascade.lean`,

shows that an empty-control fixed-modulus cascade becomes a control-block modular cascade as soon as
one supplies a nonempty separated block family with constant external degree modulo `q` on the top
host.

So the present obstruction is no longer "find a weaker terminal host collapse." It is:

> **produce or propagate the external-block residue data on the top host of a fixed-modulus witness / empty-control cascade.**

However, the zero-cost version is already impossible: the script
`verify_d0_empty_control_external_block_bridge_counterexample.py` checks `K_2`, where the whole graph
is already a fixed-modulus cascade witness of size `q = 2`, but there is no room for any nonempty
separated control block. So the live target is a **positive-cost / one-more-exponent** external-block
bridge, not the literal `D = 0` case.

## Critical path

### 1. Expose the honest asymptotic frontier

`RegularInducedSubgraph/Modular/Asymptotic.lean` now exposes
`HasPolynomialCostEmptyControlExternalBlockBridge` and the positive-dyadic self-target
`HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge`, but these are now known to be
**equivalent repackagings** of the corresponding terminal control-block modular cascade bridges. So
they are still useful bookkeeping layers, but they are not genuinely weaker theorem targets. With
`D = 0` already refuted, the live theorem target is therefore a **positive-cost / successor**
terminal bridge together with the finite data it needs.

### 2. Prove the finite external-block bridge

The next finite theorem should start from a large fixed-modulus witness or empty-control
fixed-modulus cascade and produce:

- a top host `s`,
- an empty-control cascade chain from `s`,
- a nonempty separated control-block family on `s`,
- and `HasConstantModExternalBlockDegrees` for that family.

This is the literal missing input needed by the control-block modular cascade bridge.

### 3. Attack external-block data production

This is the real mathematical step left on the modular-control side.

The most promising subproblems are:

1. **Strengthen the host-step / host-iteration machinery.**  
   The current host refinement already manufactures separated control blocks and ambient/host modular
   degree data; try to upgrade it so one also gets the modular dropped-part datum needed for a genuine
   cascade step.

2. **Pair bucketing on ambient and dropped-part data.**  
   Use the existing `Fin q × Fin q` bucketing lemmas to freeze both the relevant ambient residue class
   and the residue into the next dropped piece, rather than only the host degree.

3. **Separated-block bookkeeping from the start.**  
   Treat the dropped pieces as explicit blocks while refining the cascade, so that the external-block
   data are propagated inductively instead of reconstructed only at the terminal stage.

The right success criterion is not "more host language"; it is an actual theorem producing the
external-block data without losing too much of the terminal set.

## Strategic branches

### Branch A: direct budget-`1` collapse

This branch is now **refuted**. The script
`verify_q8_terminal_host_counterexample.py` exhibits a graph on `11` vertices with:

- an exact-card fixed-modulus single-control modular host witness of size `8` at modulus `8`;
- equivalently, a bounded fixed-modulus control-block modular host witness of size `8` with budget
  `1`;
- no regular induced subgraph on at least `8` vertices.

So neither `HasExactCardFixedSingleControlHostTerminalRegularization` nor
`HasBoundedFixedModulusControlBlockModularHostTerminalRegularization 1` can hold in full
generality. The cubic forcing-threshold shortcut remains a valid conditional implication, but it is
no longer a realistic theorem target.

### Branch B: dyadic lift plus external-block bridge

With Branch A ruled out, the dyadic program becomes the main line: prove the empty-control lift and
then bridge into the control-block modular cascade package by supplying the missing external-block
data.

The current Lean surface now makes the surviving targets explicit:

- `HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge`
  asks only for the self-bridge at positive dyadic moduli `q = 2^j` with `j > 0`, avoiding the
  impossible `q = 1` terminal control-block case;
- `HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge`
  is the corresponding data-explicit self-target. The new equivalence theorem shows that it is not
  actually weaker than the terminal self-bridge; it just exposes the missing external-block data on
  the terminal bucket;
- `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge`
  is the new honest finite self-target behind the dropped-part route: from a bounded host witness of
  size `q * q`, recover a bounded exact single-control witness of size `q` with control budget
  `q - 1`;
- `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`
  is the richer self-target that matches the current `Cascade.lean` output exactly: from the full
  refinement-data package (ambient modular degrees, exact control degree, host modular degree, and
  residual external-block data), recover a bounded exact single-control witness of size `q`. This
  immediately implies the stripped step-exact bridge and all of its downstream regularization
  wrappers;
- `hasExactCardFixedModulusSingleControlModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_self`
  records what the current host-step theorem already delivers: the `q * q -> q` self-step produces a
  structured exact-card fixed single-control modular host witness with control size exactly `q - 1`;
- `HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade`
  isolates the strongest local dropped-part route from that structured output, while
  `HasExactCardFixedSingleControlHostMaximalControlUpgrade`
  keeps only the weaker direct exact-upgrade conclusion needed downstream. These stripped upgrade
  surfaces remain useful diagnostics, but the refinement-data bridge above is now the honest theorem
  interface closest to the actual finite proof output;
- `HasPolynomialCostEmptyControlExternalBlockBridge`
  isolates the actual finite data needed to pass from the empty-control fixed-modulus cascade package
  to the control-block modular cascade package, although the script
  `verify_d0_empty_control_external_block_bridge_counterexample.py` shows that the zero-cost case is
  false already at `q = 2`. The new equivalence theorem shows that this full bridge is just a
  data-explicit presentation of the terminal control-block modular cascade bridge;
- `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge`
  isolates the strongest purely terminal bounded-host statement that would feed this route directly.

The same `q = 8` graph now also shows that the **budget-`1`** instance of this host-to-cascade
shortcut is false: `verify_q8_terminal_host_counterexample.py` finds no fixed-modulus control-block
modular cascade witness of size `8` on that graph. So Branch B can no longer factor only through a
terminal bounded-host witness.

The positive-dyadic host reductions remain useful structural reductions, but the honest live theorem
target is now the **positive-cost / successor terminal bridge together with the refinement-data exact
self-bridge above the current `Cascade` output**. The direct exact-upgrade theorem survives as the
strongest stripped benchmark, not as the primary interface.

`Asymptotic.lean` now packages that successor route explicitly:
- `hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge`
  shows that a one-step exact bridge at budget `D + 1` would yield fixed-witness terminal
  regularization at exponent `D + 2`;
- the corresponding forcing-threshold, eventual-domination, and `TargetStatement` wrappers are now
  wired through this successor route as well.

## Recommended order of attack

1. Record the `q = 8` obstruction so the false budget-`1` target does not stay on the critical path.
2. Keep the strengthened finite host/cascade packaging; it remains the right bookkeeping layer for any
   proof that manufactures external-block data.
3. Keep the new positive-dyadic bridge reductions in `Asymptotic.lean`, but treat
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge` only as a
   reduction identity, not as a realistic budget-`1` target.
4. Focus the live proof effort on proving
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`, i.e. on
   collapsing the full `q * q -> q` refinement-data package to a bounded exact single-control witness.
   Keep `HasExactCardFixedSingleControlHostMaximalControlUpgrade` as the strongest stripped benchmark
   and computational test surface below it. The stronger residue-host route is now only a diagnostic
   layer, not the main target.

The new finite self-theorem sharpens this further: the current proof already gives a structured
exact-card single-control modular host witness with control size `q - 1`, and now the code also
packages the richer refinement data that produced it. So the remaining theorem cannot factor through
the old unrestricted exact-card host regularization route—that route is already dead by the `q = 8`
counterexample. But it also cannot simply be the strongest local residue upgrade:
`verify_q4_structured_residue_upgrade_counterexample.py` shows that this stronger structured
residue-host step is already false at `q = 4`. So the live theorem has to use the special
`q - 1`-control structure and the surrounding refinement data coming from the `q * q -> q` host-step
output **without** insisting on a same-shape residue host witness.

The small dyadic cases are cleaner now as well:

- `q = 2` is trivial;
- `q = 4` is settled externally by Dyson-McKay's `N_4 = 8`, since every `16`-vertex graph already
  contains a regular induced `4`-set;
- so the first genuinely new dyadic case is `q = 8`.

## Supporting work that is useful but not on the critical path

- Keep external computational evidence separate from the formal proof line. The `q = 4` exhaustive
  search note in `notes/q4-terminal-host-search.md` is still useful reconnaissance, but it is no
  longer the reason the `q = 4` slice is known: that slice now follows from `N_4 = 8`.
- The explicit `q = 8` counterexample in `verify_q8_terminal_host_counterexample.py` is strong
  enough to rule out the old budget-`1` target, but it still does **not** identify the missing
  external-block theorem.
- The script `verify_d0_empty_control_external_block_bridge_counterexample.py` shows that the
  zero-cost external-block bridge is false already on `K_2`, so any surviving theorem must lose at
  least one extra factor of `q` before asking for a nonempty separated control-block family.
- The new equivalence theorems in `Asymptotic.lean` show that the external-block bridge formulations
  are not a separate weaker frontier. The false residue route is now exposed explicitly, and the live
  finite frontier is the richer refinement-data exact bridge above the current host-step output, with
  the direct exact upgrade as its stripped shadow.
- An exhaustive Python search found no `q = 2` counterexample to the `q * q -> q` self-step exact
  bridge up to `n = 7`. This is only computational evidence, but it supports continuing on the
  positive-dyadic self-step route rather than abandoning it.
- `verify_q4_structured_residue_upgrade_counterexample.py` is the key new pruning result: it gives a
  graph with the structured `q - 1`-control modular-host witness but no structured residue-host
  witness anywhere, while bounded exact witnesses still exist. So future proof work should target the
  richer refinement-data bridge or, at minimum, the weaker exact-upgrade theorem, not try to revive
  the residue-host route.
- The two proof heuristics worth keeping are now:
  1. completion/discrepancy on target near-regular `(q - 1)`-sets;
  2. fixed-`U` dyadic lifting through the half-obstructions `eta_m(U)`.
  The old naive balanced-halving idea should be treated only as a possible sufficient shortcut, not
  as the main formulation of the gap.
- Use `Scratch.lean` only for local theorem-shape experiments and small finite sanity checks.
- Update the README when the frontier moves, but avoid letting the documentation get ahead of the
  actual theorems.

## Things to avoid

- Do not spend time rephrasing already-settled equivalences unless they expose genuinely new finite
  data.
- Do not conflate "degrees are constant in `G[s]` on `u`" with "degrees are constant in `G[u]`".
  The whole point of the current obstruction is the missing contribution from `s \ u`.
- Do not treat the `q = 4` computation as the proof of the `q = 4` slice; it is reconnaissance,
  while the honest proof now comes from `N_4 = 8`.
- Do not treat naive balanced-halving as the core conjecture: deleted layers can reintroduce residue
  on the final `q`-set unless one controls the surviving half-obstructions `eta_m(U)`.
