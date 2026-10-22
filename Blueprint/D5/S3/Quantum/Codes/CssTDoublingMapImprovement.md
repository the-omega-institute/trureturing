# A strict distance improvement for CSS-T doubling

## Abstract

A binary cyclic map gives an admissible CSS-T extension with distance at least five, while identity doubling has distance at most four.

**Definition 1.1 (The two CSS distance legs).**

$$\forall (I: \operatorname{Type}), ([\operatorname{Fintype}\left(I\right)] \forall (C_{2}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (I \to \mathbb{F}_{2})\right)), (\forall (C_{1}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (I \to \mathbb{F}_{2})\right)), (\operatorname{cssDistance}\left(C_{2}, C_{1}\right) = \operatorname{sInf}\left((\{d: \mathbb{N} \mid \exists (x: I \to \mathbb{F}_{2}), ((x \in C_{1}) \land ((\neg (x \in C_{2})) \land (\operatorname{hammingNorm}\left(x\right) = d)))\} \cup \{d: \mathbb{N} \mid \exists (x: I \to \mathbb{F}_{2}), ((x \in \left(C_{2}\right)^{\perp}) \land ((\neg (x \in \left(C_{1}\right)^{\perp})) \land (\operatorname{hammingNorm}\left(x\right) = d)))\})\right))))$$

*Formalization.* `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.cssDistance` (`✓ std3`).

*Citation.* Elena Berardini; Reza Dastbasteh; Josu Etxezarreta Martinez; Shreyas Jain; Olatz Sanz Larrarte (2025). *Asymptotically Good CSS-T Codes and a New Construction of Triorthogonal Codes*. DOI: [10.1109/JSAIT.2025.3582156](https://doi.org/10.1109/JSAIT.2025.3582156). URL: <https://arxiv.org/abs/2412.08586v2>.

*Commentary.*

Theorem 1 defines CSS distance using the weights in C₁ outside C₂ and in C₂⊥ outside C₁⊥. Here wt is Hamming weight, orthogonality uses the binary dot product, and the infimum is taken in the natural numbers over the union of these two sets of weights. Thus the formula also specifies the empty-set convention sInf ∅ = 0 and does not assume C₂ ⊆ C₁. The index type I is any finite type.

**Definition 1.2 (The graph extension).**

$$\forall (n: \mathbb{N}), (\forall (C: \operatorname{Submodule}\left(\mathbb{F}_{2}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\forall (C_{1}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\forall (h: C \le C_{1}), (\forall (\varphi: \operatorname{LinearMap}\left(\mathbb{F}_{2}, C_{1}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\operatorname{extension}\left(h, \varphi\right) = C^{N_{\varphi}} = \{(\operatorname{val}\left(x\right), \varphi\left(\operatorname{inclusion}\left(h\right)\left(x\right)\right)) \mid x: C\})))))$$

*Formalization.* `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.extension` (`✓ std3`).

*Citation.* Elena Berardini; Reza Dastbasteh; Josu Etxezarreta Martinez; Shreyas Jain; Olatz Sanz Larrarte (2025). *Asymptotically Good CSS-T Codes and a New Construction of Triorthogonal Codes*. DOI: [10.1109/JSAIT.2025.3582156](https://doi.org/10.1109/JSAIT.2025.3582156). URL: <https://arxiv.org/abs/2412.08586v2>.

*Commentary.*

Definition 3 writes C^{Nφ} = {(x, φ(x)) : x ∈ C}. For C ⊆ C₁, the map φ is linear on C₁ and is restricted to C through the inclusion determined by h. In the formula, inclusion(h) maps C to C₁ and val is the underlying vector. A pair of vectors denotes the corresponding function on Fin(n) ⊕ Fin(n), so the extension is a binary linear code of length 2n.

**Definition 1.3 (Triple-product parity).**

$$\forall (n: \mathbb{N}), (\forall (C_{2}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\forall (C_{1}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\forall (h: C_{2} \le C_{1}), (\forall (\varphi: \operatorname{LinearMap}\left(\mathbb{F}_{2}, C_{1}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), ((\operatorname{admissible}\left(C_{2}, C_{1}, h, \varphi\right)) \Leftrightarrow (\forall (x: C_{1}), (\forall (y: C_{1}), (\forall (z: C_{2}), ((\sum_{i: \operatorname{Fin}\left(n\right)}(\operatorname{val}\left(x\right)\left(i\right) \cdot \operatorname{val}\left(y\right)\left(i\right) \cdot \operatorname{val}\left(z\right)\left(i\right))) + (\sum_{i: \operatorname{Fin}\left(n\right)}(\varphi\left(x\right)\left(i\right) \cdot \varphi\left(y\right)\left(i\right) \cdot \varphi\left(\operatorname{inclusion}\left(h\right)\left(z\right)\right)\left(i\right))) = 0)))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.admissible` (`✓ std3`).

*Citation.* Elena Berardini; Reza Dastbasteh; Josu Etxezarreta Martinez; Shreyas Jain; Olatz Sanz Larrarte (2025). *Asymptotically Good CSS-T Codes and a New Construction of Triorthogonal Codes*. DOI: [10.1109/JSAIT.2025.3582156](https://doi.org/10.1109/JSAIT.2025.3582156). URL: <https://arxiv.org/abs/2412.08586v2>.

*Commentary.*

Proposition 1 requires the sum of the two triple-product weights to be even for every x,y ∈ C₁ and z ∈ C₂. Over the binary field, this is exactly the displayed equality to zero of the two coordinate sums. The linearity of φ is part of its type. The inclusion determined by h supplies the argument of φ when z belongs to C₂.

**Definition 1.4 (A map with better distance than identity).**

$$(\operatorname{claim}) \Leftrightarrow (\exists (n: \mathbb{N}), (\exists (C_{2}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\exists (C_{1}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\exists (h: C_{2} \le C_{1}), ((\operatorname{finrank}\left(\mathbb{F}_{2}, C_{2}\right) < \operatorname{finrank}\left(\mathbb{F}_{2}, C_{1}\right)) \land (\exists (\varphi: \operatorname{LinearMap}\left(\mathbb{F}_{2}, C_{1}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), ((\operatorname{admissible}\left(C_{2}, C_{1}, h, \varphi\right)) \land (\operatorname{cssDistance}\left(\operatorname{extension}\left(h, \varphi\right), \operatorname{extension}\left(\operatorname{leRefl}\left(C_{1}\right), \varphi\right)\right) > \operatorname{cssDistance}\left(\operatorname{extension}\left(h, \operatorname{subtype}\left(C_{1}\right)\right), \operatorname{extension}\left(\operatorname{leRefl}\left(C_{1}\right), \operatorname{subtype}\left(C_{1}\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.claim` (`✓ std3`).

*Citation.* Elena Berardini; Reza Dastbasteh; Josu Etxezarreta Martinez; Shreyas Jain; Olatz Sanz Larrarte (2025). *Asymptotically Good CSS-T Codes and a New Construction of Triorthogonal Codes*. DOI: [10.1109/JSAIT.2025.3582156](https://doi.org/10.1109/JSAIT.2025.3582156). URL: <https://arxiv.org/abs/2412.08586v2>.

*Commentary.*

Remark 1 asks for maps φ giving better parameters than the identity or a permutation. The existential statement asks for a nested binary code pair of positive dimension difference and an admissible linear map whose extension has strictly greater CSS distance than identity doubling of that same pair. The first argument of cssDistance is the smaller code. Here leRefl(C₁) is the reflexive inclusion C₁ ⊆ C₁, and subtype(C₁) is the inclusion into the ambient vector space, which gives the identity choice of φ. Both extensions have length 2n and dimension dim C₁ − dim C₂.

**Theorem 1.5 (A cyclic length-thirteen construction).**

$$\exists (n: \mathbb{N}), (\exists (C_{2}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\exists (C_{1}: \operatorname{Submodule}\left(\mathbb{F}_{2}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), (\exists (h: C_{2} \le C_{1}), ((\operatorname{finrank}\left(\mathbb{F}_{2}, C_{2}\right) < \operatorname{finrank}\left(\mathbb{F}_{2}, C_{1}\right)) \land (\exists (\varphi: \operatorname{LinearMap}\left(\mathbb{F}_{2}, C_{1}, (\operatorname{Fin}\left(n\right) \to \mathbb{F}_{2})\right)), ((\operatorname{admissible}\left(C_{2}, C_{1}, h, \varphi\right)) \land (\operatorname{cssDistance}\left(\operatorname{extension}\left(h, \varphi\right), \operatorname{extension}\left(\operatorname{leRefl}\left(C_{1}\right), \varphi\right)\right) > \operatorname{cssDistance}\left(\operatorname{extension}\left(h, \operatorname{subtype}\left(C_{1}\right)\right), \operatorname{extension}\left(\operatorname{leRefl}\left(C_{1}\right), \operatorname{subtype}\left(C_{1}\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.result` (`✓ std3`). ∎

*Resolves.* `Problems/berardini-et-al-2024-csst-doubling-map-improvement` (proved) by `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"berardini-et-al-2024-csst-doubling-map-improvement","declaration_gid":"D5/S3/Quantum/Codes/CssTDoublingMapImprovement.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Elena Berardini; Reza Dastbasteh; Josu Etxezarreta Martinez; Shreyas Jain; Olatz Sanz Larrarte (2025). *Asymptotically Good CSS-T Codes and a New Construction of Triorthogonal Codes*. DOI: [10.1109/JSAIT.2025.3582156](https://doi.org/10.1109/JSAIT.2025.3582156). URL: <https://arxiv.org/abs/2412.08586v2>.

*Commentary.*

Write vectors of length 26 as two blocks over 𝔽₂¹³. Take C₁ = {(x,x) : x ∈ 𝔽₂¹³} and C₂ = {(x,x) : Σᵢ xᵢ = 0}. Their dimensions are 13 and 12. Let (Ax)ᵢ = xᵢ + xᵢ₊₁ + xᵢ₊₂, with indices modulo 13, and set φ(x,x) = (Ax,Ax). Every vector of C₁ and of φ(C₁) has two equal blocks, so each triple product has even weight and the admissibility condition holds. Identity doubling sends (x,x) to (x,x,x,x). Taking x to be a coordinate unit vector gives a vector outside the smaller extension of weight 4, hence identity distance at most 4. For the φ-extension a nontrivial X vector is (x,x,Ax,Ax) with Σᵢ xᵢ = 1, of weight 2(wt(x) + wt(Ax)). If wt(x) = 1, then wt(Ax) = 3. Otherwise wt(x) ≥ 3 and Ax ≠ 0: Ax = 0 would imply xᵢ₊₃ = xᵢ, hence x is constant because 3 is coprime to 13, and then x = 0. Thus the X-distance is at least 8. For a nontrivial Z vector (a,b,c,d), orthogonality to the smaller extension and failure of orthogonality to the larger one give a + b + Aᵀ(c + d) = 𝟙. Put w = c + d and j = wt(w). Its total weight is at least wt(w) + wt(𝟙 + Aᵀw) = j + 13 − wt(Aᵀw). The transpose is a sum of three coordinate permutations, so wt(Aᵀw) ≤ 3 wt(w). If j ≤ 4 the total weight is at least 13 − 2j ≥ 5; if j ≥ 5 it is already at least 5. Consequently the new distance is at least 5, strictly greater than the identity bound 4, at length 52 and encoded dimension 1.

## References

- Truth anchor: `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.admissible`
- Truth anchor: `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.claim`
- Truth anchor: `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.cssDistance`
- Truth anchor: `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.extension`
- Truth anchor: `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.result`
