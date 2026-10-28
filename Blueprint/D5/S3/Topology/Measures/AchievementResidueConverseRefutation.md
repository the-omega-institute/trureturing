# Indexed multigeometric achievement sets and residues

## Abstract

Indexed infinite achievement sets refute the unnormalized residue converse.

The question concerns positive weakly decreasing indexed natural coefficients, with repeated positions independently selectable. Its two source locations are Section 2, Problem 9 of Achievement sets — current results and open problems, and Section 5.1, Problem 1 of Kenyon theorem revisited. They state one question. The original coefficients are retained, without division by their greatest common divisor.

**Definition 1.1 (Distinct indexed Boolean block sums).**

$$\begin{aligned}\forall (m : \mathbb{N}), \forall (k : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \\\operatorname{blockSums}\left(k\right) = \operatorname{image}\left((b : \operatorname{Fin}\left(m\right) \to Bool) \mapsto \sum_{i: \operatorname{Fin}\left(m\right)} \operatorname{ite}\left(\operatorname{b}\left(i\right), \operatorname{k}\left(i\right), 0\right), \operatorname{univ}\left(\operatorname{Fin}\left(m\right) \to Bool\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.blockSums` (`✓ std3`).

*Citation.* Szymon Głąb and Franciszek Prus-Wiśniowski (2025). *Achievement sets — current results and open problems*. URL: <https://arxiv.org/abs/2512.17285v1>.

*Commentary.*

For every implicit m : ℕ and k : Fin m → ℕ, blockSums k : Finset ℕ is Finset.univ.image (fun b : Fin m → Bool => ∑ i, if b i then k i else 0). The universal finite set ranges over every Boolean function on Fin m, including when m = 0. ite is the Boolean if-then-else operation. Only equal sum values are identified; equal coefficients at distinct indices remain independent choices.

**Definition 1.2 (The original infinite source sequence).**

$$\begin{aligned}\forall (m : \mathbb{N}), \forall (hm : 0 < m), \forall (k : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (n : \mathbb{N}), \forall (t : \mathbb{N}), \\\operatorname{sourceTerm}\left(hm, k, n, t\right) = \frac{\operatorname{realCast}\left(\operatorname{k}\left(\langle\operatorname{mod}\left(t, m\right), \operatorname{modLt}\left(t, hm\right)\rangle\right)\right)}{(\operatorname{realCast}\left(n\right))^{\operatorname{natDiv}\left(t, m\right)+1}}\end{aligned}$$

*Formalization.* `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.sourceTerm` (`✓ std3`).

*Citation.* Szymon Głąb and Franciszek Prus-Wiśniowski (2025). *Achievement sets — current results and open problems*. URL: <https://arxiv.org/abs/2512.17285v1>.

*Commentary.*

For every implicit m : ℕ, hm : 0 < m, k : Fin m → ℕ and n t : ℕ, sourceTerm hm k n t : ℝ equals (k ⟨t % m, Nat.mod_lt t hm⟩ : ℝ) / (n : ℝ) ^ (t / m + 1). Here mod is natural remainder, natDiv is natural quotient, modLt is the proof Nat.mod_lt, and realCast is coercion to ℝ. Thus t = jm + i selects the original position i in block j, and the first denominator exponent is one. The definition itself imposes no positivity, ordering or n > 1 hypothesis; these enter claim.

**Definition 1.3 (Genuine convergent subseries).**

$$\begin{aligned}\forall (m : \mathbb{N}), \forall (hm : 0 < m), \forall (k : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (n : \mathbb{N}), \\\operatorname{achievement}\left(hm, k, n\right) = \{ x: \mathbb{R} \mid \exists (A : \operatorname{Set}\left(\mathbb{N}\right)), \operatorname{HasSum}\left((t : A) \mapsto \operatorname{sourceTerm}\left(hm, k, n, \operatorname{val}\left(t\right)\right), x\right) \}\end{aligned}$$

*Formalization.* `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.achievement` (`✓ std3`).

*Citation.* Szymon Głąb and Mateusz Kula (2025). *Kenyon theorem revisited*. URL: <https://arxiv.org/abs/2508.19454v1>.

*Commentary.*

For every implicit m : ℕ, hm : 0 < m, k : Fin m → ℕ and n : ℕ, achievement hm k n : Set ℝ is exactly {x | ∃ A : Set ℕ, HasSum (fun t : A => sourceTerm hm k n t.val) x}. The binder t : A ranges over the subtype of original indices lying in A. HasSum is the actual infinite-series convergence relation. A may be any subset, including the empty set or an infinite set; no finite approximation or interval is part of the definition.

**Definition 1.4 (The full unnormalized residue implication).**

$$claim \Leftrightarrow \begin{aligned}\forall (m : \mathbb{N}), \forall (hm : 0 < m), \forall (k : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (n : \mathbb{N}), \\(\forall (i : \operatorname{Fin}\left(m\right)), 0 < \operatorname{k}\left(i\right)) \Rightarrow \operatorname{Antitone}\left(k\right) \Rightarrow 1 < n \Rightarrow \\\operatorname{card}\left(\operatorname{blockSums}\left(k\right)\right) = n \Rightarrow \\(\forall (i : \operatorname{Fin}\left(m\right)), \neg (n \mid \operatorname{k}\left(i\right))) \Rightarrow \\0 < \operatorname{volume}\left(\operatorname{achievement}\left(hm, k, n\right)\right) \Rightarrow \\\operatorname{image}\left((s : \mathbb{N}) \mapsto \operatorname{mod}\left(s, n\right), \operatorname{blockSums}\left(k\right)\right) = \operatorname{range}\left(n\right)\end{aligned}$$

*Formalization.* `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.claim` (`✓ std3`).

*Citation.* Szymon Głąb and Franciszek Prus-Wiśniowski (2025). *Achievement sets — current results and open problems*. URL: <https://arxiv.org/abs/2512.17285v1>.

*Commentary.*

The closed definition claim : Prop has the exact body: ∀ (m : ℕ) (hm : 0 < m) (k : Fin m → ℕ) (n : ℕ), (∀ i, 0 < k i) → Antitone k → 1 < n → (blockSums k).card = n → (∀ i, ¬ n ∣ k i) → 0 < volume (achievement hm k n) → (blockSums k).image (fun s => s % n) = Finset.range n.

All indices i range over Fin m. Antitone means weakly decreasing in this index order, not strictly decreasing. card counts distinct block-sum values, volume is Lebesgue measure on ℝ, and image and range are the finite-set operations. There is no coprimality, primitive-coefficient, normalization or distinct-coefficient assumption.

**Theorem 1.5 (Negation of the full residue implication).**

$$\neg (\begin{aligned}\forall (m : \mathbb{N}), \forall (hm : 0 < m), \forall (k : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (n : \mathbb{N}), \\(\forall (i : \operatorname{Fin}\left(m\right)), 0 < \operatorname{k}\left(i\right)) \Rightarrow \operatorname{Antitone}\left(k\right) \Rightarrow 1 < n \Rightarrow \\\operatorname{card}\left(\operatorname{blockSums}\left(k\right)\right) = n \Rightarrow \\(\forall (i : \operatorname{Fin}\left(m\right)), \neg (n \mid \operatorname{k}\left(i\right))) \Rightarrow \\0 < \operatorname{volume}\left(\operatorname{achievement}\left(hm, k, n\right)\right) \Rightarrow \\\operatorname{image}\left((s : \mathbb{N}) \mapsto \operatorname{mod}\left(s, n\right), \operatorname{blockSums}\left(k\right)\right) = \operatorname{range}\left(n\right)\end{aligned})$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem is result : ¬ claim, with no free parameters or hypotheses. The proposition negated has the exact body: ∀ (m : ℕ) (hm : 0 < m) (k : Fin m → ℕ) (n : ℕ), (∀ i, 0 < k i) → Antitone k → 1 < n → (blockSums k).card = n → (∀ i, ¬ n ∣ k i) → 0 < volume (achievement hm k n) → (blockSums k).image (fun s => s % n) = Finset.range n.

Take m = 3, k = (9, 3, 3) and n = 6. The distinct block sums are {0, 3, 6, 9, 12, 15}, so their cardinality is six and their residues modulo six are {0, 3}; residue one is missing. The coefficients are positive and weakly decreasing, and none is divisible by six.

For each subset A of the original indices, Nat.divModEquiv 3 regroups its genuinely summable subseries into blocks. Each Boolean block has value 3d for a digit d ∈ Fin 6. The resulting HasSum equals 3 * Real.ofDigits (selectedDigits A). Conversely, digitBits selects the two repeated coefficient positions independently and realizes every base-six digit. Applying this selection at every block realizes every digit sequence as a subset of the original indices. Real.ofDigits_SurjOn and Real.ofDigits_le_one therefore give achievement (by decide : 0 < 3) coefficients 6 = Set.Icc 0 3 in both directions, including endpoints. Real.volume_Icc supplies positive Lebesgue measure, contradicting the full residue conclusion.

The source sequence starts with denominator exponent one. The interval endpoint printed in the surrounding Nitecki theorem has a different scale; the argument here uses the actual HasSum equality instead of that endpoint. The tuple has a common factor three. Dividing it out changes residues modulo six and changes the assertion. Statements requiring primitive or normalized coefficients are separate questions and are not established here.

## References

- Truth anchor: `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.achievement`
- Truth anchor: `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.blockSums`
- Truth anchor: `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.claim`
- Truth anchor: `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.result`
- Truth anchor: `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.sourceTerm`
