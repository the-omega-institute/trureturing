# Automatic discrepancy of complementary anti-recurrences

## Abstract

Every positive integral anti-recurrence has a unique complementary source and a finite automaton for its exact discrepancy.

**Theorem 1.1 (The whole positive coefficient family).**

$$\forall k \in \mathrm{Nat},\; \forall a \in \operatorname{Functions}\left(\operatorname{Fin}\left(k\right), \mathrm{Nat}\right),\; 1 < k \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(k\right),\; 0 < \operatorname{a}\left(j\right)\right) \Rightarrow \left(\exists A \in \mathrm{NatToNat},\; \exists B \in \mathrm{NatToNat},\; \operatorname{Source}\left(k, a, A, B\right) \land \left(\left(\forall Aprime \in \mathrm{NatToNat},\; \forall Bprime \in \mathrm{NatToNat},\; \operatorname{Source}\left(k, a, Aprime, Bprime\right) \Rightarrow \left(Aprime = A \land Bprime = B\right)\right) \land \operatorname{Automatic}\left(\operatorname{trace}\left(k, a\right), \operatorname{discrepancy}\left(k, a, A\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/AntiRecurrenceAutomaticity.result` (`✓ std3`). ∎

*Resolves.* `Problems/fokkink-joshi-whole-antirecurrence-automaticity` (proved) by `D5/S1/Recurrence/AntiRecurrenceAutomaticity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fokkink-joshi-whole-antirecurrence-automaticity","declaration_gid":"D5/S1/Recurrence/AntiRecurrenceAutomaticity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Fix k > 1 and a positive integral vector (a₁,…,aₖ). In the formal vector a : Fin k → Nat, entry j represents the source coefficient aⱼ₊₁. Write τ = Σ aⱼ and H = kτ, so τ ≥ k ≥ 2. NatToNat denotes the natural sequences. Source requires A₀ = B₀ = 0, strict increase of both sequences, and, for every positive integer x, membership in A at a positive index exactly when x is absent from B at positive indices. Its recurrence is Aₙ = Σⱼ₌₁ᵏ aⱼ Bₖ₍ₙ₋₁₎₊ⱼ for every n ≥ 1. Strict increase and the zero values imply positivity of all source terms. The zero values are auxiliary.

The discrepancy is dₙ = Aₙ − (H+1)n in Int. Automatic(τ,d) means that there exist a type Q with Fintype Q and a native DFAO with input Fin τ and integer output whose output on the standard base-τ expansion of n, most significant digit first, is dₙ. The equation holds at every positive n, including the entire initial segment. The definition also handles n = 0 using the empty digit word and d₀ = 0. The remainder used to coerce digits into Fin τ changes no standard digit, since each digit is smaller than τ.

Existence is established before automaticity. After constructing the first n values of A, enumerate the positive integers outside that finite history. The next value of A is the weighted sum of the next block of k enumerated values. Positivity of the coefficients and k > 1 place this new value strictly above the entire block. Inserting it therefore preserves all enumerated values through that block. This stabilization defines the infinite increasing B. The history grows monotonically, successive positive A terms have gaps at least kτ, and stabilization proves disjointness, exhaustion and the exact recurrence. Any other complementary source has the same successive blocks by induction, and hence the same A and B.

For a positive complement index m, let t be the number of positive A terms strictly below Bₘ. Complementarity gives Bₘ = m+t and Aₜ < Bₘ < Aₜ₊₁. Equivalently, Aₜ−t < m ≤ Aₜ₊₁−(t+1). The map t ↦ Aₜ−t is nondecreasing, so these two inequalities determine the rank t uniquely. In discrepancy coordinates the weaker strict bounds are Ht+dₜ < m < Ht+H+1+dₜ₊₁.

Put c = Σⱼ₌₁ᵏ aⱼ(j−k). For n ≥ 1 let mⱼ = k(n−1)+j and let tⱼ be the rank belonging to Bₘⱼ. Substituting Bₘⱼ = mⱼ+tⱼ into the source recurrence gives dₙ = c + Σ aⱼtⱼ − n and the balance identity H dₙ = (H+1)c + Σ aⱼ(Htⱼ−mⱼ). These are identities for one common source; each inverse rank is taken in that same A/B pair.

The bound uses strong induction rather than assuming a bounded error. For n ≥ N = 4H+4, the gap estimate implies tⱼ+1 < n. Let E = Σ₀≤ᵢ<N |dᵢ| and D = E+(k+1)|c|+H+1. Earlier discrepancy bounds and the inverse inequalities give |Htⱼ−mⱼ| ≤ H+1+D. Thus |H dₙ| ≤ (H+1)|c|+τ(H+1+D) ≤ HD. The final inequality uses k ≥ 2 and τ ≥ 1. The finite initial segment is bounded by E. Consequently |dₙ| ≤ D for all n.

Boundedness supplies a finite local rule for the actual inverse ranks. Set W = D+2(H+1)+k+2 and R = W+1. For q ≥ R and a digit r < τ, each rank used at n = τq+r differs from q by an integer in [−W,W]. If p ≥ R and the discrepancy windows of radius R at q and p agree, transfer the two inequalities defining each rank from q to p. Rank uniqueness makes the signed offsets tⱼ−q and t′ⱼ−p equal. The discrepancy formula then gives dτq+r = dτp+r. This proves the local rule for every vector.

The automaton is built directly from this rule. Extend d to negative integers by zero only for the window construction. Set L = 2τ(R+2) and M = R+L+2. The feature at n consists of min(n,M) and the padded window (dₙ₊z) for −L ≤ z ≤ L. There are finitely many features because each entry lies in [−D,D]. A feature with n < M identifies its index exactly. For larger indices, Euclidean division of r+z by τ reduces every child-window entry to the proved local rule. Equal features therefore have equal features after n ↦ τn+r. Reachable features form the DFAO states; the central window entry is the output. Induction on input words proves evaluation at their Horner value, and the standard digit-value theorem gives the required output at every n.

The source is Fokkink and Joshi, Anti-Recurrence Sequences, arXiv:2506.13337v1, Conjecture 4, and INTEGERS 26, A24, DOI 10.5281/zenodo.18305140, Conjecture 2. The accompanying Library entry records source rights and the exact correspondence. The all-ones and other source-proved restricted families receive no separate new credit. Uniform discrepancy boundedness is a weaker consequence within the proof. The machine and constants depend on the vector; minimality, an executable generator and a runtime bound are not asserted.

## References

- Truth anchor: `D5/S1/Recurrence/AntiRecurrenceAutomaticity.result`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](../../S0/Automata/DFAOStateLowerBound.md)
