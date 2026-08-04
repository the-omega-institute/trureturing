# Receipt absorption sweep (2026-08-04)

Scope: the 30 unique Scribe document groups whose receipts were aligned by commit
`2c3736c`.  Those groups cover 45 ledger atoms.  This audit asks only whether an
atom has uncarried content while claiming `migration: absorbed` with no unresolved
subitems.  It does not reassess coverage admission or change coverage semantics.

Method: first classify every aligned atom from `Meta/BACKFILL.yaml`.  A `partial`
atom with a nonempty unresolved list cannot make the false-absorption promise in
question.  Inspect the source CAS bytes and covered Lean/Scribe declaration for
each remaining `absorbed` plus empty-unresolved candidate.  The sweep found one
false promise: GICT theorem/7.4.  It is resolved with action B (partial plus explicit
unresolved subitems), because its only coverage GID carries the fixed-point
equivalence but not the source atom's operator-plus-selection-principle claim.

## Candidate decisions

- GICT theorem/7.4 source says a definition needs an operator plus a selection
  principle (`Meta/Digestion/atoms/sha256/9b7a3ffc25dbae19ef334f68bbfdc9182d64e32492f99436316099057780b1da:1`).
  Its only coverage target states the pointwise fixed-point equivalence
  (`D5/S1/Dynamics/RecursiveDefinition.lean:28`).  Independent selection results
  exist at `D5/S1/Dynamics/RecursiveDefinition.lean:34` and
  `D5/S1/Dynamics/RecursiveDefinition.lean:50`, but they have no coverage receipt
  for this atom.  Action B records `extremal-fixed-point-selection-principle` and
  `unique-fixed-point-selection-collapse` as unresolved at
  `Meta/BACKFILL.yaml:2811` and makes migration partial at
  `Meta/BACKFILL.yaml:2817`.
- The other six candidates are faithfully carried: Li causal trichotomy source
  (`Meta/Digestion/atoms/sha256/1614202e858b8782b7da0a289033669a0d5e5f5d3b138200a3c892b6e5a81c11:1`)
  is carried at `D5/S3/Analytic/LiCausalTrichotomy.lean:612`; prime-factorization
  existence (`Meta/Digestion/atoms/sha256/0c12d6f29b67f19afd7260e90da96e6c8522e6bda9d50a46d407ddb19fc4d2ed:1`)
  at `D5/S3/Arith/PrimeFactorization.lean:14`; residue separation
  (`Meta/Digestion/atoms/sha256/20f648ea5c78c25c814862a3eb098cdc4b6a8ad9d578a3f4177b448a6a6d3841:1`)
  at `D5/S3/Arith/ResidueSeparation.lean:22`; Euclid's lemma
  (`Meta/Digestion/atoms/sha256/e9155bfb8e91559618a98ef8a368e0131b4decb9f8a86accf03a9dc1c6f21eea:1`)
  at `D5/S3/Arith/EuclidLemma.lean:14`; hidden-fiber rigidity
  (`Meta/Digestion/atoms/sha256/19d504af31c9add47a2f4e0f1c44efc82d5447e8a418dacc7eeb17ac7af7677f:1`)
  at `D5/S3/Arith/HiddenFiberRigidity.lean:38`; and jump-cocycle consistency
  (`Meta/Digestion/atoms/sha256/2bf22a61c83cffae0134a75dff11aa487139dba7ba1cb1c154e81ef6004e052d:1`)
  at `D5/S1/Dynamics/JumpCocycle.lean:20`.

## All 30 groups

Each `BACKFILL` reference is the atom's entry start.  Counts are the number of
explicit unresolved subitems.  Repeated atoms appear under every Scribe group
whose receipt they use, so all 30 groups remain independently enumerable.

| # | Scribe group | Atom evidence | Result |
|---:|---|---|---|
| 1 | `D5/S1/Scale/CarrierFoundations` | `Meta/BACKFILL.yaml:2165` | partial, unresolved=2; no false-absorption promise |
| 2 | `D5/S1/Scale/FibonacciEigen` | `Meta/BACKFILL.yaml:2478` | partial, unresolved=3; no false-absorption promise |
| 3 | `D5/S3/Constants/ElementaryExactValues` | `Meta/BACKFILL.yaml:2520` | partial, unresolved=2; no false-absorption promise |
| 4 | `D5/S1/Dynamics/KnasterTarskiWitness` | `Meta/BACKFILL.yaml:2737` | partial, unresolved=2; prior correction preserved |
| 5 | `D5/S1/Dynamics/RecursiveDefinition` | `Meta/BACKFILL.yaml:2794` | action B; partial, unresolved=2 |
| 6 | `D5/S3/Analytic/LiCausalTrichotomy` | `Meta/BACKFILL.yaml:3203` | absorbed candidate inspected; faithfully carried |
| 7 | `D5/S1/Phase/ZeroOrbitCongruence` | `Meta/BACKFILL.yaml:4362`, `Meta/BACKFILL.yaml:20115` | partial, unresolved=5 each |
| 8 | `D5/S1/Phase/SeatTowerCombinatorics` | `Meta/BACKFILL.yaml:4362`, `Meta/BACKFILL.yaml:4418`, `Meta/BACKFILL.yaml:4606`, `Meta/BACKFILL.yaml:20115`, `Meta/BACKFILL.yaml:20171`, `Meta/BACKFILL.yaml:20345` | all partial, unresolved nonempty |
| 9 | `D5/S1/Phase/SeatTowerArithmetic` | `Meta/BACKFILL.yaml:4503`, `Meta/BACKFILL.yaml:4606`, `Meta/BACKFILL.yaml:20249`, `Meta/BACKFILL.yaml:20345` | all partial, unresolved nonempty |
| 10 | `D5/S1/Phase/WalkFormula` | `Meta/BACKFILL.yaml:4503`, `Meta/BACKFILL.yaml:20249` | partial, unresolved nonempty |
| 11 | `D5/S1/Depth/TwelveScaleReduction` | `Meta/BACKFILL.yaml:4606`, `Meta/BACKFILL.yaml:20345` | partial, unresolved nonempty |
| 12 | `D5/S1/Depth/PartialQuotientExtraction` | `Meta/BACKFILL.yaml:4606`, `Meta/BACKFILL.yaml:20345` | partial, unresolved nonempty |
| 13 | `D5/S1/Depth/StationingCombinatorics` | `Meta/BACKFILL.yaml:4606`, `Meta/BACKFILL.yaml:20345` | partial, unresolved nonempty |
| 14 | `D5/S1/Phase/SeatTowerConsequences` | `Meta/BACKFILL.yaml:4606`, `Meta/BACKFILL.yaml:20345` | partial, unresolved nonempty |
| 15 | `D5/S3/Arith/PrimeFactorization` | `Meta/BACKFILL.yaml:7107` | absorbed candidate inspected; faithfully carried |
| 16 | `D5/S1/Deficit/DeficitInteger` | `Meta/BACKFILL.yaml:7637` | partial, unresolved=3; prior correction preserved |
| 17 | `D5/S3/Weil/ReflectionLedger` | `Meta/BACKFILL.yaml:7829`, `Meta/BACKFILL.yaml:12085`, `Meta/BACKFILL.yaml:12449`, `Meta/BACKFILL.yaml:12480`, `Meta/BACKFILL.yaml:12567`, `Meta/BACKFILL.yaml:12602`, `Meta/BACKFILL.yaml:12635` | all partial, unresolved nonempty |
| 18 | `D5/S3/Arith/ResidueSeparation` | `Meta/BACKFILL.yaml:9479` | absorbed candidate inspected; faithfully carried |
| 19 | `D5/S3/Arith/EuclidLemma` | `Meta/BACKFILL.yaml:9550` | absorbed candidate inspected; faithfully carried |
| 20 | `D5/S3/Arith/HiddenFiberRigidity` | `Meta/BACKFILL.yaml:10733` | absorbed candidate inspected; faithfully carried |
| 21 | `D5/S1/Dynamics/JumpCocycle` | `Meta/BACKFILL.yaml:10811` | absorbed candidate inspected; faithfully carried |
| 22 | `D5/S3/Zeros/CompletedZeta` | `Meta/BACKFILL.yaml:11210`, `Meta/BACKFILL.yaml:11249`, `Meta/BACKFILL.yaml:11461` | all partial, unresolved nonempty |
| 23 | `D5/S3/Analytic/CompletedZetaMellinReconstruction` | `Meta/BACKFILL.yaml:11341` | partial, unresolved=1 |
| 24 | `D5/S3/Zeros/EulerWindows` | `Meta/BACKFILL.yaml:11610` | partial, unresolved=6 |
| 25 | `D5/S3/Weil/SpectralDynamics` | `Meta/BACKFILL.yaml:11792`, `Meta/BACKFILL.yaml:11955`, `Meta/BACKFILL.yaml:12041`, `Meta/BACKFILL.yaml:12685`, `Meta/BACKFILL.yaml:12719`, `Meta/BACKFILL.yaml:12770`, `Meta/BACKFILL.yaml:12910` | all partial, unresolved nonempty |
| 26 | `D5/S3/Weil/SpectralHilbert` | `Meta/BACKFILL.yaml:11817` | partial, unresolved=3 |
| 27 | `D5/S3/Zeros/SpectralShift` | `Meta/BACKFILL.yaml:11882` | partial, unresolved=6 |
| 28 | `D5/S1/Scale/MinkowskiModelSet` | `Meta/BACKFILL.yaml:11927` | partial, unresolved=5 |
| 29 | `D5/S3/Weil/EulerProduct` | `Meta/BACKFILL.yaml:12532`, `Meta/BACKFILL.yaml:15407` | partial, unresolved nonempty |
| 30 | `D5/S3/Weil/CriticalLine` | `Meta/BACKFILL.yaml:15443` | partial, unresolved=9 |

Result: 30/30 groups checked, seven absorbed/empty candidates inspected, one false
promise found and corrected.  The two earlier corrections remain partial and
explicitly unresolved.
