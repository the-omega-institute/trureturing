# A quadratic-field counterexample to the rank-only Jensen converse

## Abstract

A signed quadratic norm gives an all-input counterexample to the unrestricted rank-only Jensen converse.

The source is Barczy and Pales, Jensen convex functions and doubly stochastic matrices, arXiv:2510.03715v1, Remark 2.2(i), referring to Theorem 2.1(i), equation (2.1), and Definition 1.1. Jensen convexity there means midpoint convexity. The question replaces the theorem's special column-span condition by real rank at least two. It imposes no continuity, measurability, boundedness, rational-entry condition or extra column-span assumption.

In the formula, Fin(n) is the finite type with n coordinates and I in a function type is the original interval subtype. Every arithmetic mean is the displayed subtype constructor ⟨∑(j : Fin n), (n : ℝ)⁻¹ * (x j : ℝ), hI.sum_mem⟩, with weights proved nonnegative from n > 0, total weight proved one using that same hypothesis, and each x j membership supplied by (x j).property. Every matrix row is the displayed subtype constructor ⟨∑(j : Fin n), P i j * (x j : ℝ), hI.sum_mem⟩, whose weight hypotheses are the nonnegativity and row-sum components of hP. The casts are the subtype values (x j : ℝ), so the formula uses the actual mean and row outputs in I rather than display abbreviations. The native doublyStochastic set requires every entry to be nonnegative and every row and column sum to be one.

**Definition 1.1 (The complete original universal converse).**

$$\operatorname{claim} = \left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall I \in \operatorname{Set}\left(\mathbb{R}\right),\; \operatorname{Nonempty}\left(I\right) \Rightarrow \left(\operatorname{IsOpen}\left(I\right) \Rightarrow \left(\forall hI \in \operatorname{Convex}\left(\mathbb{R}, I\right),\; \forall f \in I \to \mathbb{R},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall hP \in P \in \operatorname{doublyStochastic}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; 2 \le \operatorname{rank}\left(P\right) \Rightarrow \left(\left(\forall x \in \operatorname{Fin}\left(n\right) \to I,\; f\left(\langle\sum_{(j : \operatorname{Fin}\left(n\right))} ((n : \mathbb{R}))^{-1} \cdot (x\left(j\right) : \mathbb{R}), hI.sum_{mem}\rangle\right) \le \frac{\sum_{(i : \operatorname{Fin}\left(n\right))} f\left(\langle\sum_{(j : \operatorname{Fin}\left(n\right))} P\left(i\right)\left(j\right) \cdot (x\left(j\right) : \mathbb{R}), hI.sum_{mem}\left((fun j \mathord{\cdot} \mapsto (\operatorname{mem_{doublyStochastic_{iff_{sum}}}}.mp\left(hP\right)).1\left(i, j\right)), (\operatorname{mem_{doublyStochastic_{iff_{sum}}}}.mp\left(hP\right)).2.1\left(i\right), (fun j \mathord{\cdot} \mapsto (x\left(j\right)).property)\right)\rangle\right)}{n}\right) \Rightarrow \left(\forall u \in I,\; \forall v \in I,\; f\left(\langle\sum_{(j : \operatorname{Fin}\left(2\right))} ((2 : \mathbb{R}))^{-1} \cdot (![u, v]\left(j\right) : \mathbb{R}), hI.sum_{mem}\rangle\right) \le \frac{f\left(u\right) + f\left(v\right)}{2}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/BarczyPalesJensenConverse.claim` (`✓ std3`).

*Citation.* Mátyás Barczy; Zsolt Páles (2025). *Jensen convex functions and doubly stochastic matrices*. URL: <https://arxiv.org/abs/2510.03715v1>.

*Commentary.*

For every positive integer n, every nonempty open convex subset I of the real line, every arbitrary function f from I itself to the reals, and every real n by n doubly stochastic matrix P of real rank at least two, the inequality f applied to the displayed subtype arithmetic mean is at most the average of f applied to the displayed subtype matrix rows for every x in I^n is asserted to imply midpoint convexity for every u and v in I. Nonempty open convex subsets of the real line are exactly the open intervals in scope, including unbounded intervals and the whole line. The antecedent compares the actual arithmetic-mean input with the actual matrix row images for all inputs. The claim is a closed proposition and contains no restriction of arbitrary subtype functions to functions supplied with an ambient extension. The compiled declaration is D5.S3.QuadraticForms.BarczyPalesJensenConverse.claim.

**Theorem 1.2 (Negation of the complete converse).**

$$\neg (\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall I \in \operatorname{Set}\left(\mathbb{R}\right),\; \operatorname{Nonempty}\left(I\right) \Rightarrow \left(\operatorname{IsOpen}\left(I\right) \Rightarrow \left(\forall hI \in \operatorname{Convex}\left(\mathbb{R}, I\right),\; \forall f \in I \to \mathbb{R},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall hP \in P \in \operatorname{doublyStochastic}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; 2 \le \operatorname{rank}\left(P\right) \Rightarrow \left(\left(\forall x \in \operatorname{Fin}\left(n\right) \to I,\; f\left(\langle\sum_{(j : \operatorname{Fin}\left(n\right))} ((n : \mathbb{R}))^{-1} \cdot (x\left(j\right) : \mathbb{R}), hI.sum_{mem}\rangle\right) \le \frac{\sum_{(i : \operatorname{Fin}\left(n\right))} f\left(\langle\sum_{(j : \operatorname{Fin}\left(n\right))} P\left(i\right)\left(j\right) \cdot (x\left(j\right) : \mathbb{R}), hI.sum_{mem}\left((fun j \mathord{\cdot} \mapsto (\operatorname{mem_{doublyStochastic_{iff_{sum}}}}.mp\left(hP\right)).1\left(i, j\right)), (\operatorname{mem_{doublyStochastic_{iff_{sum}}}}.mp\left(hP\right)).2.1\left(i\right), (fun j \mathord{\cdot} \mapsto (x\left(j\right)).property)\right)\rangle\right)}{n}\right) \Rightarrow \left(\forall u \in I,\; \forall v \in I,\; f\left(\langle\sum_{(j : \operatorname{Fin}\left(2\right))} ((2 : \mathbb{R}))^{-1} \cdot (![u, v]\left(j\right) : \mathbb{R}), hI.sum_{mem}\rangle\right) \le \frac{f\left(u\right) + f\left(v\right)}{2}\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/BarczyPalesJensenConverse.result` (`✓ std3`). ∎

*Resolves.* `Problems/barczy-2025-unrestricted-jensen-converse` (refuted) by `D5/S3/QuadraticForms/BarczyPalesJensenConverse.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barczy-2025-unrestricted-jensen-converse","declaration_gid":"D5/S3/QuadraticForms/BarczyPalesJensenConverse.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mátyás Barczy; Zsolt Páles (2025). *Jensen convex functions and doubly stochastic matrices*. URL: <https://arxiv.org/abs/2510.03715v1>.

*Commentary.*

The entire universal claim is false: there exist a positive dimension, a nonempty open real interval, an actual function on that interval and an actual real doubly stochastic matrix of rank at least two for which the comparison holds at every input but midpoint convexity fails. The witness uses n=3 and I equal to the whole real line. The source definition and the result have literal types Prop and Not claim, respectively.

Let s=sqrt(3). The implemented field K is QuadraticAlgebra Q 3 0, with omega=(0,1) and omega^2=3. The rational nonsquare fact follows from the existing prime nonsquare theorem. QuadraticAlgebra.lift sends a+b*omega to a+b*s in the reals. Its field homomorphism is injective, identifying K with the actual embedded field Q(s). The real K-algebra and scalar module are induced by this embedding. Applying the existing vector-space linear splitting to the injective K-linear embedding gives a total K-linear left inverse L from all real numbers to K, fixing every embedded field element. This is an actual classical-choice construction; no retraction, scalar certificate or regularity hypothesis is added.

Define F(x) to be the rational-to-real cast of N(L(x)), where N(a+b*omega)=a^2-3*b^2 is the signed quadratic norm. L need only be K-linear; its multiplicativity is never asserted. On I=univ the witness subtype function sends an interval element x to F(x.val). All interval membership proofs are supplied by the convex-combination constructors.

The actual matrix is P=(1/12)*[[5,3,4],[s+2,6-s,4],[5-s,3+s,4]]. The bounds 1<s<2 prove nonnegative entries, and each row and column sums to one. The top-left two by two minor has determinant (3-s)/18, which is positive. The existing determinant-rank and submatrix-rank theorems therefore give real rank at least two for this same matrix.

For an arbitrary real triple x, set m=(x(0)+x(1)+x(2))/3 and t=(x(0)-x(1))/12. Direct matrix multiplication gives Px=(m+t,m+(s-2)*t,m+(1-s)*t). K-linearity of L transports these three entries to A+B, A+(omega-2)*B and A+(1-omega)*B, with A=L(m) and B=L(t). For all A,B in K, direct expansion of the quadratic norm gives N(A+B)+N(A+(omega-2)*B)+N(A+(1-omega)*B)=3*N(A). After rational casting this proves sum_i F((Px)(i))=3*F(m) for every real input. There is no division by input-dependent quantities, rational-input restriction or finite-sample substitution. The source inequality holds with equality at every legal input.

Retraction fixes s and -s, so F(s)=F(-s)=-3 and F(0)=0. Applying the alleged midpoint conclusion to the two interval elements s and -s would require 0<=-3. The contradiction uses the complete universal converse through its legal n=3 witness; it does not merely negate a witness-only surrogate.

This mathematical result concerns the exact unrestricted v1 question. The paper's positive theorem under its original column-span hypothesis and its forward Jensen-convexity implications are not contradicted. Regularity-restricted variants are separate questions.

## References

- Truth anchor: `D5/S3/QuadraticForms/BarczyPalesJensenConverse.claim`
- Truth anchor: `D5/S3/QuadraticForms/BarczyPalesJensenConverse.result`
