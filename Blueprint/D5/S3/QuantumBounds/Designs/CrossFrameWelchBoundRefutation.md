# A dual-frame counterexample to the cross-Gramian Welch bound

## Abstract

A spanning family of three nonzero vectors in the real plane and its dual have cross-Gramian coherence 3/19, below the proposed Welch bound 1/3.

**Definition 1.1 (Finite-dimensional frames).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (\operatorname{IsFrame}\left(F\right)) \Leftrightarrow (\operatorname{span}\left(\mathbb{R}, \operatorname{range}\left(F\right)\right) = \operatorname{top})$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.IsFrame` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Definition 1 (arXiv:2205.05613v3, p. 3) defines a frame by positive lower and finite upper bounds for the sum of squared analysis coefficients. The source then states verbatim: "In a finite-dimensional space H, frames are simply spanning sets of H." IsFrame uses this characterization: the real linear span of the range of F is the whole Euclidean space. Fin k indexes the k vectors from zero, and EuclideanSpace R (Fin n) is the standard real n-dimensional Hilbert space. The condition k >= n is supplied in claim.

**Definition 1.2 (Both dual reconstruction equations).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (\operatorname{IsDualFrame}\left(F, G\right)) \Leftrightarrow ((\operatorname{IsFrame}\left(G\right)) \land ((\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \sum_{i: \operatorname{Fin}\left(k\right)} \langle x, \operatorname{G}\left(i\right) \rangle \cdot \operatorname{F}\left(i\right) = x) \land (\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \sum_{i: \operatorname{Fin}\left(k\right)} \langle x, \operatorname{F}\left(i\right) \rangle \cdot \operatorname{G}\left(i\right) = x)))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.IsDualFrame` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Definition 3 (p. 3): "Let {f_i}_{i=1}^k be a frame for H. A dual frame for {f_i}_{i=1}^k is a frame {g_i}_{i=1}^k such that for every f ∈ H," followed by f = sum_i <f,g_i> f_i = sum_i <f,f_i> g_i. IsDualFrame includes that G is a frame and both equations, with x denoting the source's f. The assumption that F is a frame appears separately in claim. All inner products and scalar multiplications are over R.

**Definition 1.3 (Maximal off-diagonal magnitude).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \operatorname{coherence}\left(F, G\right) = \operatorname{iSup}\left(\lambda p: \operatorname{Subtype}\left(\lambda q: \operatorname{Fin}\left(k\right) \times \operatorname{Fin}\left(k\right), \operatorname{Prod.fst}\left(q\right) \ne \operatorname{Prod.snd}\left(q\right)\right), \left|\langle \operatorname{F}\left(\operatorname{Prod.fst}\left(\operatorname{val}\left(p\right)\right)\right), \operatorname{G}\left(\operatorname{Prod.snd}\left(\operatorname{val}\left(p\right)\right)\right) \rangle\right|\right)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.coherence` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Section 4 (p. 12): "Let F = {f₁, …, fₖ} be a frame for Fⁿ, and let H = {h₁, …, hₖ} be a dual frame for F. We denote the cross-Gramian of F and H by Gr(F, H) and we denote the maximal off-diagonal magnitude of Gr(F, H) as" followed by µ(Gr(F, H)) := max_{i≠j} |⟨f_i, h_j⟩|. Here G denotes H. coherence is the supremum over the subtype of pairs (i,j) with i ≠ j. For k >= 2 the finite index set is nonempty, so this is precisely the source's maximum. Subtype takes the displayed predicate on pairs; val extracts the underlying pair, and Prod.fst and Prod.snd are its two projections.

**Definition 1.4 (Conjecture 41).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (n \le k) \Rightarrow ((2 \le k) \Rightarrow ((\operatorname{IsFrame}\left(F\right)) \Rightarrow ((\operatorname{IsDualFrame}\left(F, G\right)) \Rightarrow (\sqrt{\frac{\operatorname{val}\left(n\right) \cdot \operatorname{val}\left(k\right) - \operatorname{val}\left(n\right)^{2}}{\operatorname{val}\left(k\right)^{2} \cdot (\operatorname{val}\left(k\right) - 1)}} \le \operatorname{coherence}\left(F, G\right))))))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.claim` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Conjecture 41 (Section 4.2, p. 17), verbatim: "Let F be a frame for Fⁿ, and let G be one of its dual frames. Then" µ(Gr(F, G)) ≥ √((nk − n²)/(k²(k − 1))). (21) The encoding takes the real case of the source's field R or C. It quantifies all n, k and all vector families F, G, with n <= k and 2 <= k so that the off-diagonal maximum is nonempty. The operator val denotes the natural-to-real cast; every subtraction and the division in the square root are in R.

Five-column application exposition: a complete real dual family and the energy-step obstruction. Use one-based matrix indices in this application. Let F = [[1,0,0,-1,0],[0,1,0,0,-1],[0,0,1,0,0]], with columns f₁ = e₁, f₂ = e₂, f₃ = e₃, f₄ = −e₁ and f₅ = −e₂ in real Euclidean three-space. A real 3 by 5 matrix G represents its five column vectors gⱼ, not its three rows. The matrix equations FGᵀ = I₃ and GFᵀ = I₃ are equivalent by transposition; acting on any vector y they give y = ∑ⱼ ⟨y,gⱼ⟩fⱼ = ∑ⱼ ⟨y,fⱼ⟩gⱼ. Reconstruction expresses every y as a linear combination of either family, so both span. Thus these equations give actual duals in the existing IsFrame and IsDualFrame senses, including both reconstruction sums.

Reconstruction and all real parameters. For an arbitrary real G = (gᵣⱼ), right multiplication gives GFᵀ = [[g₁₁−g₁₄,g₁₂−g₁₅,g₁₃],[g₂₁−g₂₄,g₂₂−g₂₅,g₂₃],[g₃₁−g₃₄,g₃₂−g₃₅,g₃₃]]. Equating this to I₃ imposes all nine identities: g₁₁−g₁₄ = 1, g₁₂−g₁₅ = 0, g₁₃ = 0; g₂₁−g₂₄ = 0, g₂₂−g₂₅ = 1, g₂₃ = 0; g₃₁−g₃₄ = 0, g₃₂−g₃₅ = 0, g₃₃ = 1. Set a = g₁₁, b = g₁₂, c = g₂₁, d = g₂₂, e = g₃₁ and f = g₃₂. These recover the unique parameter tuple of G and force G = [[a,b,0,a−1,b],[c,d,0,c,d−1],[e,f,1,e,f]]. Conversely, substitution verifies every one of the nine equations for every a,b,c,d,e,f ∈ R. There are no sign, positivity or size restrictions on these six parameters for duality. Equivalently, this entire affine fiber is its central dual plus the kernel of right multiplication by Fᵀ.

Cross-Gram entries and coherence. The real column inner products are Cᵢⱼ = ⟨fᵢ,gⱼ⟩, so C = FᵀG = [[a,b,0,a−1,b],[c,d,0,c,d−1],[e,f,1,e,f],[−a,−b,0,1−a,−b],[−c,−d,0,−c,1−d]]. In row order, the twenty ordered off-diagonal entries are C₁₂ = b, C₁₃ = 0, C₁₄ = a−1, C₁₅ = b; C₂₁ = c, C₂₃ = 0, C₂₄ = c, C₂₅ = d−1; C₃₁ = e, C₃₂ = f, C₃₄ = e, C₃₅ = f; C₄₁ = −a, C₄₂ = −b, C₄₃ = 0, C₄₅ = −b; C₅₁ = −c, C₅₂ = −d, C₅₃ = 0, C₅₄ = −c. Therefore µ = max(|a|,|a−1|,|d|,|d−1|,|b|,|c|,|e|,|f|). This is the existing coherence definition's supremum over the finite nonempty set of unequal index pairs: all entries are bounded by the displayed maximum, and an off-diagonal entry attains each candidate magnitude. In particular, the diagonal entry C₃₃ = 1 never enters the maximum.

Energy and the full real region. Summing the squares of precisely those twenty entries gives S_off = a²+(a−1)²+d²+(d−1)²+4b²+4c²+2e²+2f² = 1+Q, where Q = 2(a−1/2)²+4b²+4c²+2(d−1/2)²+2e²+2f². The coefficients count the ordered entries, including the two occurrences each of e and f. For n = 3 and k = 5, label case (a) by 3 > 9/5+S_off and case (b) by 9/5+S_off ≥ 3. Case (a) is exactly Q < 1/5: the entire open real ellipsoid centered at (1/2,0,0,1/2,0,0), with positive quadratic weights (2,4,4,2,2,2) in the order (a,b,c,d,e,f). Every point with Q = 1/5 belongs to case (b) with equality; every point with Q > 1/5 belongs to strict case (b). These alternatives cover the unrestricted real parameter space, not just positive parameters or a small neighborhood.

The diagonal branch is independent of that region calculation. Its energy is D = a²+(1−a)²+d²+(1−d)²+1 = 2+2(a−1/2)²+2(d−1/2)² ≥ 2 > 9/5 for every real parameter tuple. Thus the strict-diagonal hypothesis D > n²/k holds even on the ellipsoid boundary and exterior. The total cross-frame energy is P = D+S_off. Although the general inequalities P ≥ n and D ≥ n²/k give S_off ≥ n−n²/k when D = n²/k, they do not give that conclusion from D > n²/k. This family computes the exact failure region of that proposed lower-bound step: S_off < 6/5 exactly in case (a). Case (b) does imply the proposed coherence bound, since S_off ≤ 20µ² and S_off ≥ 6/5.

Symmetric real section. Take a = d = 3/5 and b = c = e = f = x for every x ∈ R. The resulting actual dual is Gₓ = [[3/5,x,0,−2/5,x],[x,3/5,0,x,−2/5],[x,x,1,x,x]], and its cross-Gram matrix is [[3/5,x,0,−2/5,x],[x,3/5,0,x,−2/5],[x,x,1,x,x],[−3/5,−x,0,2/5,−x],[−x,−3/5,0,−x,2/5]]. Substitution into the full quadratic form gives Q = 1/25+12x² and S_off = 26/25+12x². Hence case (a) is equivalent to 12x² < 4/25, or −1/(5√3) < x < 1/(5√3); the division uses √3 > 0. Both endpoints x = −1/(5√3) and x = 1/(5√3) give case (b) with equality. Outside the closed interval case (b) is strict. This section consumes the full real family without replacing it.

Frame bounds and the actual canonical center. All five columns of F have norm one, and their analysis energy at y is 2|y₁|²+2|y₂|²+|y₃|². It lies between ‖y‖² and 2‖y‖²; e₃ and e₁ attain the respective bounds 1 and 2. In particular F is a frame and is not tight. Its frame operator has matrix FF* = diag(2,2,1), with inverse diag(1/2,1/2,1). Applying that inverse to the columns gives G₀ = [[1/2,0,0,−1/2,0],[0,1/2,0,0,−1/2],[0,0,1,0,0]]. This is the center a = d = 1/2, b = c = e = f = 0 of the real fiber and ellipsoid. The explicit inverse is the inverse function used by CrossFrameExclusiveDualRefutation.frameOperator and CrossFrameExclusiveDualRefutation.canonicalDual. G₀Fᵀ = FG₀ᵀ = I₃, so this canonical center is an actual dual. Its cross-Gram matrix is [[1/2,0,0,−1/2,0],[0,1/2,0,0,−1/2],[0,0,1,0,0],[−1/2,0,0,1/2,0],[0,−1/2,0,0,1/2]], with off-diagonal coherence 1/2. At the center Q = 0, S_off = 1 and D = 2; canonicality here does not make the diagonal entries all equal to n/k = 3/5.

Minimum over every actual real and complex dual. Let K be R or C and let H be any 3 by 5 matrix over K satisfying FH* = I₃, where * denotes conjugate transpose and F is the same real matrix embedded in K. Taking adjoints yields HF* = I₃. Because F has real entries, its (1,1) reconstruction equation is h₁₁−h₁₄ = 1. In C_H = F*H, the two entries (4,1) and (1,4) are −h₁₁ and h₁₄. Both are off-diagonal, so, writing t = maxᵢ≠ⱼ |(C_H)ᵢⱼ|, the triangle inequality gives 1 = |h₁₁−h₁₄| ≤ |h₁₁|+|h₁₄| ≤ 2t. Thus every actual real dual and every actual complex dual has t ≥ 1/2. The displayed real G₀, also viewed over C, satisfies the actual reconstruction identity and attains t = 1/2. Consequently the minimum is 1/2 in each field. This complex argument quantifies over all actual complex H directly; it does not infer complex exhaustiveness from the real six-parameter family. The real ellipsoid above classifies only real duals. No uniqueness, classification of all minimizers or co-equidistribution assertion follows here.

Direct application E4. Set a = d = 3/5 and b = c = e = f = 1/20, or x = 1/20 in the symmetric section. Then G = [[3/5,1/20,0,−2/5,1/20],[1/20,3/5,0,1/20,−2/5],[1/20,1/20,1,1/20,1/20]] is an actual dual by all nine reconstruction identities. Its cross-Gram matrix is [[3/5,1/20,0,−2/5,1/20],[1/20,3/5,0,1/20,−2/5],[1/20,1/20,1,1/20,1/20],[−3/5,−1/20,0,2/5,−1/20],[−1/20,−3/5,0,−1/20,2/5]]. The full formulas give Q = 7/100, S_off = 107/100 and µ = 3/5. It is in case (a), while its coherence exceeds the attainable minimum 1/2; it is not an optimal dual. The separate two-dimensional, four-column examples E1–E3 have different frames and reconstruction equations. They remain separate application residuals, with no coverage or minimum claim supplied by this five-column computation.

Connection and evidence boundary. Every actual dual of this F, real or complex, has coherence at least 1/2 > √6/10, the C41 constant for (n,k) = (3,5). Thus case (a) occurs but does not refute C41 for this frame; it only defeats the indicated energy-step justification. The refutation theorem below instead uses its own real two-dimensional, three-column frame. This five-column exposition is an independently phrased application derivation using the generic real IsFrame, IsDualFrame and coherence definitions, the cited canonical-dual semantics, and native matrix-entry, adjoint, finite-maximum, square-completion and norm-triangle operations. The public Cross-Frame Potential article supplies definitions and C41 background; it is not cited as the source of these additional calculations or a priority claim. Neither CrossFrameWelchBoundRefutation.result nor CrossFrameExclusiveDualRefutation.result is a five-column theorem. The complete application has no exact compiled Lean client attached to this narrative: its reconstruction identities, exhaustive parameterization, entry and energy formulas, region, canonical-center identification and universal real/complex minimum remain formalization residuals. A generated document or a check of the existing referenced declarations does not kernel-verify their composition.

**Theorem 1.5 (The conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/aceska-kaczanowski-2022-cross-frame-welch-bound-refutation` (refuted) by `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"aceska-kaczanowski-2022-cross-frame-welch-bound-refutation","declaration_gid":"D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Take n = 2, k = 3 and F = ((-3,-3),(-3,3),(-1,0)), with G = ((-3/19,-1/6),(-3/19,1/6),(-1/19,0)). Both reconstruction equations hold for every x. Each family therefore spans: reconstruction writes every x as a linear combination of its members. The six off-diagonal inner products are -1/38, 3/19, -1/38, 3/19, 3/19, 3/19 in the order (0,1),(0,2),(1,0),(1,2),(2,0),(2,1). Their maximum absolute value is 3/19, strictly below sqrt(1/9) = 1/3. These exact rational computations refute the universally quantified claim.

## References

- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.IsDualFrame`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.IsFrame`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.claim`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.coherence`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.result`
