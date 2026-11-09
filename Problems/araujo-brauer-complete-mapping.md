---
slug: araujo-brauer-complete-mapping
bibkey: araujo2026brauerexistence
doi: null
url: https://arxiv.org/abs/2608.25092v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.result
---

# Complete-mapping existence for Brauer and partial Brauer monoids

## Problem

Araújo, Bentz, Cameron, Hendrey and Kinyon, *Complete Mappings of Semigroups*, arXiv:2608.25092v1, Section 15, printed page 61, Problem 15.11; [preregistration #23706](https://github.com/the-omega-institute/trureturing/issues/23706).

> Classify complete mappings for $\mathcal B_n$ and $\mathcal{PB}_n$. In view of the Hall--Paige theorem, the unresolved proper factors are those of ranks $2$ and $3$ which occur in the corresponding monoid. Determine also for which values of $n$ the whole monoid has a complete mapping.

The settled question is the last sentence, for positive degrees. A complete mapping is a bijection $\alpha$ for which $x\mapsto x\alpha(x)$ is also bijective. The source asks for the degrees and does not assert the numerical answer.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Positive degree $n$ | `claim` quantifies over natural $n$ with $1\le n$ | Degree zero is outside the source question. |
| Partitions of two $n$-point rows | `Setoid (Bool × Fin n)` | `false` and `true` represent the two rows; `Fin n` shifts the paper's labels by one. |
| Every block has size two | `Brauer` and `blockSize` | Literal block-size condition. |
| Every block has size at most two | `PartialBrauer` and `blockSize` | Singleton blocks remain allowed. |
| Concatenation and exterior connectivity | `partitionProduct` | Embeds the two partitions in three rows, joins their equivalence relations and restricts to the exterior rows. |
| Complete mapping and orthomorphism both bijective | Frozen `AraujoOrthodoxCompleteMappingRefutation.CompleteMapping` | The carrier and source semigroup are explicit in `claim`. |
| Which degrees admit a complete mapping | `AraujoBrauerCompleteMapping.result` | Both families have one exactly when $n=1$ or $4\le n$, for every binding source realization. |
| Availability of the source monoid structures | The first two conjuncts of `claim` | These supply the source algebra; they add no restriction on the classification. |

## Motivation

The settling declaration is `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.result`. Its full proposition is displayed in its Blueprint Scribe. The source definitions and conventions are recorded in `Library/Certificates/araujo2026brauerexistence.md`; the existing DOI-bearing note `Library/Certificates/araujo2026completemappings.md` owns DOI `10.48550/arXiv.2608.25092`.

## Gap

Ranks two and three have symmetric groups without complete mappings. Even index permits diagonal packet transversals. At the remaining odd indices, a permutation of the half diagrams must contain a triangle whose transport has negative sign. Abstract group isomorphisms alone do not identify the actual sandwich entries.

## Route

The construction pairs adjacent through sets and extends the pairing by four vertices. Odd matching fibres yield paired half diagrams except for a designated triangle. Overlay connectivity provides the transports; the triangle holonomy has sign $-1$. The coordinate reconstruction and product theorems transfer these witnesses to the actual principal factors. Rank-fibre transversals assemble a whole-monoid complete mapping. Unit restrictions exclude degrees two and three, while identity mappings handle degree one.

The symmetric-group supplier is constructed in `AraujoSymmetricCompleteMappings.symmetric_small_or_large`. The all-parameter witnesses are `AraujoBrauerOverlayTransport.rank_two_signed_half_cycles` and `rank_three_signed_half_cycles`; `AraujoSignedFactorLifting.rank_two_signed_factor` and `rank_three_signed_factor` transfer them to the sandwich entries. These declarations occur on the settling proof's dependency path.

## Falsifier

A positive degree for which either existence equivalence fails, a source realization not covered by the explicit multiplication law, or a missing rank-coordinate correspondence would contradict the stated classification. Enumerating all individual complete mappings is a separate question. Finite computations test the specified instances and do not prove the all-degree result.

## Evidence

Kernel-checked: `AraujoBrauerCompleteMapping.result`, with axiom closure contained in $\{\mathsf{propext},\mathsf{Classical.choice},\mathsf{Quot.sound}\}$. The proof constructs both source structures and treats every realization satisfying their literal multiplication laws. The frozen complete-mapping predicate is reused directly.

### Exact computation

[Experiment directory at `99ccaef5cc5ac675599e1843f62f43158f9c6582`](https://github.com/the-omega-institute/trureturing-experiments/tree/99ccaef5cc5ac675599e1843f62f43158f9c6582/docs/reports/araujo-brauer-complete-mapping).

Program: `docs/reports/araujo-brauer-complete-mapping/check.py`; SHA-256 `76a2a1e4e3385f7ba79e6ed32bbfcb84e7d110677a6d5c5bc369ee385e508e46`. The immutable blob was checked with `git cat-file -e`. The implementation seat ran the byte-identical blob with `python3 /Users/auric/.sshx/93c4c3e0708636d3dfdaac12/attempt-1/experiment-check.py`, exit 0, final result `ALL_CHECKS_OK`.

The exact checks cover telephone counts through complement size 10; index parity through degree 40; subset-pairing extension instances through degrees 38 and 39 for ranks two and three; complete support matrices through degree five and samples in degree six; the anchored permutations on 45 indices at $(6,2)$ and 105 at $(7,3)$; complete mappings of $B_1,PB_1,B_4,PB_4$ on respectively 1, 2, 105 and 764 diagrams; and the unit-ideal obstruction on every diagram product in degrees two and three. The Brandt matrix-unit fidelity checks find 2 and 12 mappings in orders two and three. These are finite readings.

### Escape audit

The four-slot escape audit is unfinished for the new public theorems: [#24053](https://github.com/the-omega-institute/trureturing/issues/24053). The source-family realization, lawful enrolled readout, equivalence bridge and intervention/dependence evidence are not compiled. No `declared_validated` registration is asserted.

## Triage

1. **Proved, kernel-checked:** nominated signed witnesses exist for every $k\ge0$ in degrees $6+4k$ at rank two and $7+4k$ at rank three. Evidence: `AraujoBrauerOverlayTransport.rank_two_signed_half_cycles` and `rank_three_signed_half_cycles`.
2. **Proved, kernel-checked:** both identity laws and associativity hold for literal `partitionProduct` on all partitions. Evidence: `AraujoBrauerSourceMonoids.partitionProduct_identity_left`, its consumed private `partitionProduct_identity_right`, and `partitionProduct_assoc`.
3. **Proved, kernel-checked:** partial matching counts on any finite type with at least two vertices are even. Evidence: `AraujoBrauerSourceMonoids.partial_matching_card_even`, using the inversion-parity count in `partial_matching_card_mod_two`.
4. **Computed:** the exact checker verifies complete mappings of $B_4$ and $PB_4$ on 105 and 764 diagrams, and the unit-ideal obstruction in degrees two and three. Evidence: the immutable experiment entry, command, exit 0 and SHA-256 above.
5. **Proved, kernel-checked:** for both families and every source realization, the positive-degree existence classification is $n=1$ or $n\ge4$; degrees two and three are excluded. Evidence: `AraujoBrauerCompleteMapping.result`.
6. **Open:** classifying or enumerating every individual complete mapping is outside the existence target.
7. **Proved, kernel-checked:** adjacent-fixed-set connectivity holds for arbitrary finite vertex types and involutions under the stated fixed-set difference hypotheses. Finiteness is retained. Evidence: the consumed private `AraujoBrauerOverlayTransport.adjacent_fixed_sets_connected`; its full hypotheses appear in its Lean statement.
8. **Proved, kernel-checked:** the constructive symmetric-group supplier works for every $r\ge4$. Evidence: `AraujoSymmetricCompleteMappings.symmetric_small_or_large` specialized to $r\ne2,3$, using its consumed private `symmetric_complete_mapping` and `symmetric_option_lift`.
9. **Open (supplemental computation unverified):** the independent finite check of the $S_3$ local fibre packets and $C_2$ residual transversals has no immutable program in the pinned experiment directory. The corresponding general constructions are kernel-checked on the settling path; this item makes no additional computational claim.
10. **Proved, kernel-checked:** the all-$k$ signed witnesses survive the rank-coordinate bridge to the actual sandwich entries. Evidence: `AraujoSignedFactorLifting.rank_two_signed_factor` and `rank_three_signed_factor`.
11. **Proved, kernel-checked:** the nominated infinite families have principal-factor transversal permutations. Evidence: `AraujoSignedFactorLifting.rank_two_signed_factor` and `rank_three_signed_factor`, whose conclusions are `Nonempty ReesTransversal` for the actual half-diagram matrix.
12. **Proved, kernel-checked:** the unit-permutation identification extends to every degree and every binding source realization. Evidence: the consumed private `AraujoBrauerCompleteMapping.brauer_units_perm` and `partial_units_perm`.

### What the settlement shows

The decisive obstruction is concentrated in the rank-two and rank-three factors. Even index permits paired packets; the odd-index families use one triangle with negative transport sign. This settles the whole-monoid existence clause and supplies the nominated unresolved factors. It does not enumerate all mappings or settle every proper factor in the excluded small degrees. The connectivity lemma retains arbitrary finite carriers; no infinite-carrier extension is asserted. The source's other results require no altered hypothesis from this existence classification.

## ASSUMED-UNVERIFIED

Literature-screen completeness and priority are `ASSUMED-UNVERIFIED`. The preregistration records the literature reading; no exhaustive literature search is claimed. The supplementary finite packet computation and the four-slot escape audit remain unverified as specified above.
