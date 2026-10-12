# Variable-exponent Hornich–Hlawka refutation

## Abstract

A two-valued variable exponent gives a Luxemburg norm violating the Hornich–Hlawka inequality.

Marinescu and Niculescu, A survey of the Hornich-Hlawka inequality, arXiv:2407.03278v1, §3, the paragraph introducing Problem 3 and Problem 3 itself, verbatim: “A natural generalization of Lp spaces is provided by the class of Lp(·) spaces with variable exponent. They differ from the classical Lp spaces in that the exponent p is not constant but a function from the measure space under attention to [1, ∞]. See the monograph of L. Diening, P. Harjulehto, P. Hästö and M. Ruzicka [6] for a thorough presentation. Problem 3. Is every Lp(·)(0, 1) space with a variable exponent p(·) : (0, 1) → [1, 2] a Hornich-Hlawka space?”

**Definition 1.1 (The variable-exponent modular).**

$$\operatorname{modular}\left(p, f, lam\right) = \int^{-}_{t \in (0, 1)} \operatorname{ofReal}\left(\left|\frac{\operatorname{f}\left(t\right)}{lam}\right|^{\operatorname{p}\left(t\right)}\right) dt$$

*Formalization.* `D5/S3/Geometry/VariableExponentHornichHlawka.modular` (`✓ std3`).

*Citation.* D.-Ş. Marinescu; C. P. Niculescu (2024). *A survey of the Hornich-Hlawka inequality*. URL: <https://arxiv.org/abs/2407.03278v1>.

*Commentary.*

For real functions p and f and a real scale lam, modular is the Lebesgue lower integral on (0,1) of ENNReal.ofReal (|f(t)/lam| raised to p(t)). Its values are extended nonnegative reals. The scale is restricted to positive values in the norm and membership definitions.

**Definition 1.2 (The Luxemburg norm).**

$$\operatorname{luxNorm}\left(p, f\right) = \operatorname{sInf}\left(\{ lam: \mathbb{R} \mid (0 < lam) \land (\operatorname{modular}\left(p, f, lam\right) \le 1) \}\right)$$

*Formalization.* `D5/S3/Geometry/VariableExponentHornichHlawka.luxNorm` (`✓ std3`).

*Citation.* D.-Ş. Marinescu; C. P. Niculescu (2024). *A survey of the Hornich-Hlawka inequality*. URL: <https://arxiv.org/abs/2407.03278v1>.

*Commentary.*

The real infimum is taken over positive scales with modular at most one. Functions are represented on the real line, with the integral restricted to (0,1). The definition is the Luxemburg norm on the variable-exponent space, using the convention of Diening, Harjulehto, Hästö and Ruzicka cited in §3 of the survey.

**Definition 1.3 (Variable-exponent membership).**

$$\operatorname{InLp}\left(p, f\right) \Leftrightarrow \left((\operatorname{Measurable}\left(f\right)) \land (\exists lam: \mathbb{R}, (0 < lam) \land (\operatorname{modular}\left(p, f, lam\right) \le 1))\right)$$

*Formalization.* `D5/S3/Geometry/VariableExponentHornichHlawka.InLp` (`✓ std3`).

*Citation.* D.-Ş. Marinescu; C. P. Niculescu (2024). *A survey of the Hornich-Hlawka inequality*. URL: <https://arxiv.org/abs/2407.03278v1>.

*Commentary.*

InLp p f requires measurability of the representative on the real line and a positive scale at which the modular is at most one. For exponents bounded between one and two, this is the scaled-modular membership condition. The counterexample functions satisfy global measurability and therefore give measurable representatives on (0,1).

**Definition 1.4 (The universal Hornich–Hlawka claim).**

$$claim \Leftrightarrow (\forall p: \mathbb{R} \to \mathbb{R}, (\operatorname{Measurable}\left(p\right)) \Rightarrow ((\forall t: \mathbb{R}, (t \in (0, 1)) \Rightarrow ((1 \le \operatorname{p}\left(t\right)) \land (\operatorname{p}\left(t\right) \le 2))) \Rightarrow (\forall f: \mathbb{R} \to \mathbb{R}, \forall g: \mathbb{R} \to \mathbb{R}, \forall h: \mathbb{R} \to \mathbb{R}, (\operatorname{InLp}\left(p, f\right)) \Rightarrow ((\operatorname{InLp}\left(p, g\right)) \Rightarrow ((\operatorname{InLp}\left(p, h\right)) \Rightarrow (\operatorname{luxNorm}\left(p, f + g\right) + \operatorname{luxNorm}\left(p, g + h\right) + \operatorname{luxNorm}\left(p, h + f\right) \le \operatorname{luxNorm}\left(p, f\right) + \operatorname{luxNorm}\left(p, g\right) + \operatorname{luxNorm}\left(p, h\right) + \operatorname{luxNorm}\left(p, f + g + h\right)))))))$$

*Formalization.* `D5/S3/Geometry/VariableExponentHornichHlawka.claim` (`✓ std3`).

*Citation.* D.-Ş. Marinescu; C. P. Niculescu (2024). *A survey of the Hornich-Hlawka inequality*. URL: <https://arxiv.org/abs/2407.03278v1>.

*Commentary.*

The formal encoding of Problem 3 quantifies over measurable real exponents p with 1≤p(t)≤2 for t in (0,1), and every triple f, g, h satisfying InLp p. It requires the sum of the three pair-sum Luxemburg norms to be at most the sum of the three individual norms and the triple-sum norm. The definitions use representatives; the integrals and strict violation depend only on their almost-everywhere classes. For constant p in [1,2], the survey's isometric embedding into L¹ gives a positive answer.

**Theorem 1.5 (A two-valued exponent refutes the claim).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/VariableExponentHornichHlawka.result` (`✓ std3`). ∎

*Resolves.* `Problems/marinescu-niculescu-2024-variable-exponent-hornich-hlawka` (refuted) by `D5/S3/Geometry/VariableExponentHornichHlawka.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"marinescu-niculescu-2024-variable-exponent-hornich-hlawka","declaration_gid":"D5/S3/Geometry/VariableExponentHornichHlawka.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D.-Ş. Marinescu; C. P. Niculescu (2024). *A survey of the Hornich-Hlawka inequality*. URL: <https://arxiv.org/abs/2407.03278v1>.

*Commentary.*

Let p(t)=1 for t<1/2 and p(t)=2 otherwise. The private lemmas exponent_measurable and exponent_range prove the hypotheses. For u=(a,b,c), let J(u) equal 4a on (0,1/4), 4b on [1/4,1/2), √2 c on [1/2,1), and zero elsewhere. The lemma modular_J gives (|a|+|b|)/lam+c²/lam² at every positive scale. Writing A=|a|+|b|, scale_iff identifies modular≤1 with N(a,b,c)≤lam, where N=(A+√(A²+4c²))/2. The lemmas luxNorm_J and J_InLp give this norm and membership whenever N>0. Take x=J(0,1,1/2), y=J(0,−1,1/2), z=J(−1,0,−1/2). N_special gives ‖x‖=‖y‖=‖z‖=‖x+y+z‖=(1+√2)/2; J_add and pair_norms give ‖x+y‖=1 and ‖y+z‖=‖z+x‖=2. Since √2<3/2, the inequality would require 5≤2+2√2<5. This answers Problem 3 negatively. As mathematical reasoning, J identifies a three-dimensional subspace with the Luxemburg norm of |a|+|b|+c², a nonlinear mixture of an ℓ¹ and an ℓ² part; each part separately embeds in L¹. A linear isometry and the norm axioms are not separately formalized. Problem 4 for variable-exponent Sobolev spaces is unsettled for positive derivative order; W⁰ is L, so order zero inherits the example. Continuous exponents, exponents close to constant, and a classification of the Hornich–Hlawka exponents remain unsettled. The journal full text is ASSUMED-UNVERIFIED. Persistence of the strict violation when the two powers move slightly into (1,2) is also ASSUMED-UNVERIFIED: continuity of the seven finite-sum modular unit levels gives the reasoning, but no perturbation theorem or quantitative radius is formalized. The quotation refers to arXiv:2407.03278v1, §3, Problem 3.

## References

- Truth anchor: `D5/S3/Geometry/VariableExponentHornichHlawka.InLp`
- Truth anchor: `D5/S3/Geometry/VariableExponentHornichHlawka.claim`
- Truth anchor: `D5/S3/Geometry/VariableExponentHornichHlawka.luxNorm`
- Truth anchor: `D5/S3/Geometry/VariableExponentHornichHlawka.modular`
- Truth anchor: `D5/S3/Geometry/VariableExponentHornichHlawka.result`
