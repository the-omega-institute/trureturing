# The Garden-of-Eden Theorem

## Abstract

The Moore–Myhill theorem equates surjectivity and finite-difference preinjectivity for every finite-alphabet two-sided local rule.

Let A be any finite alphabet, including the empty and singleton alphabets, and let k be any natural number. A local rule h takes a word indexed by Fin(k+2) to a letter of A. The native code sends an arbitrary integer configuration x to the configuration whose value at i is h applied to j ↦ x(i+j). BipermutativeLift.code, BipermutativeLift.window and BipermutativePreinjectivity.Preinjective refer to the original declarations in the PermutativeLifts namespaces; the theorem imposes no permutativity, endpoint injectivity or local bijectivity condition. Preinjectivity quantifies over all x,y : Z → A with finite {i | x(i) ≠ y(i)} and identical complete code images.

**Definition 1.1 (Insert a finite word in an arbitrary context).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall n: \mathbb{N},\\\forall p: (\operatorname{Fin}(n) \to A),\\\forall t: \mathbb{Z},\\\forall z: (\mathbb{Z} \to A),\\\forall i: \mathbb{Z},\\\operatorname{writeWord}(p, t, z, i) = \operatorname{ifThenElse}(t \le i \land i < t + \operatorname{cast}(n), \operatorname{p}(\operatorname{Fin.mk}(\operatorname{Int.toNat}(i - t))), \operatorname{z}(i))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/GardenOfEden.writeWord` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

writeWord(p,t,z) places p at sites t through t+n-1 and agrees with z elsewhere. Inside the interval the Fin index is (i-t).toNat; its bound follows from t≤i<t+n. The finite word may have length zero, and the ambient configuration has no support restriction.

**Theorem 1.2 (A finite collision supplies universally replaceable words).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall k: \mathbb{N},\forall h: ((\operatorname{Fin}(k + 2) \to A) \to A),\\\neg \operatorname{BipermutativePreinjectivity.Preinjective}(h) \Rightarrow\\\exists n: \mathbb{N},\\0 < n \land\\\exists p: (\operatorname{Fin}(n) \to A),\\\exists q: (\operatorname{Fin}(n) \to A),\\p \neq q \land\\\forall t: \mathbb{Z},\\\forall z: (\mathbb{Z} \to A),\\(\forall j: \operatorname{Fin}(n),\operatorname{z}(t + \operatorname{cast}(j)) = \operatorname{p}(j)) \Rightarrow\\\operatorname{BipermutativeLift.code}(h, \operatorname{writeWord}(q, t, z)) = \operatorname{BipermutativeLift.code}(h, z)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/GardenOfEden.exists_erasable_words` (`✓ std3`). ∎

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

No alphabet finiteness is required for this replacement statement. A failure of native preinjectivity gives distinct configurations with a finite disagreement set and equal complete images. Enclose that set in [a,b] and retain the collar [a-(k+1),b+(k+1)]. Every local output window touching the disagreement core lies inside the collar. A window missing the core is unchanged; a window touching it compares with the two original colliding windows. Restrict the colliding configurations to the padded interval and translate that interval to Fin(n). The resulting distinct words p,q have positive common length, and any occurrence of p at any integer site can be replaced by q without changing any output coordinate.

**Definition 1.3 (The actual spatial image language).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall k: \mathbb{N},\forall h: ((\operatorname{Fin}(k + 2) \to A) \to A),\\\forall z: (\mathbb{N} \to A),\\z \in \operatorname{imageRay}(h) \iff\\\exists x: (\mathbb{Z} \to A),\\\forall n: \mathbb{N},\\\operatorname{z}(n) = \operatorname{BipermutativeLift.code}(h, x, \operatorname{cast}(n))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/GardenOfEden.imageRay` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

imageRay(h) consists exactly of restrictions to natural coordinates of full integer code images. Its prefixCount is the number of Fin(n) words actually realized in those images. For a nonempty alphabet it is nonempty and invariant under the one-sided spatial shift. PrefixGrowthEntropy.prefix_growth_entropy therefore supplies its real logarithmic growth limit.

**Theorem 1.4 (A finite collision forces strict actual image-prefix growth loss).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\{}[\operatorname{Finite}(A)],\\\forall k: \mathbb{N},\forall h: ((\operatorname{Fin}(k + 2) \to A) \to A),\\2 \le \operatorname{Nat.card}(A) \land \neg \operatorname{BipermutativePreinjectivity.Preinjective}(h) \Rightarrow\\\exists r: \mathbb{R},\\r < \operatorname{Real.log}(\operatorname{cast}(\operatorname{Nat.card}(A))) \land\\\operatorname{Tendsto}((n: \mathbb{N} \mapsto \operatorname{Real.log}(\operatorname{cast}(\operatorname{PrefixGrowthEntropy.prefixCount}(\operatorname{imageRay}(h), n)))/\operatorname{cast}(n)), atTop, \operatorname{nhds}(r))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/GardenOfEden.strict_image_prefix_loss` (`✓ std3`). ∎

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

Write q=Nat.card(A)≥2. The conclusion gives a real r strictly below log(q), together with convergence of n ↦ log(prefixCount(imageRay(h),n))/n to r. This counts spatial prefixes of complete images; it is not temporal entropy of iterations of code(h).

Take the replaceable words p,q of common length m>0. On n disjoint tiles, replace each occurrence of p by q. The code image is preserved, and every normalized block avoids p. The normalized blocks and a tail of length k+1 determine the first nm output coordinates, so the actual count is at most (card(A)^m−1)^n card(A)^(k+1). Passing to the already existing prefix-growth limit gives r≤log(card(A)^m−1)/m<log(card(A)).

**Theorem 1.5 (Surjectivity is equivalent to native preinjectivity).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\{}[\operatorname{Finite}(A)],\\\forall k: \mathbb{N},\forall h: ((\operatorname{Fin}(k + 2) \to A) \to A),\\\operatorname{Function.Surjective}(\operatorname{BipermutativeLift.code}(h)) \iff \operatorname{BipermutativePreinjectivity.Preinjective}(h)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/GardenOfEden.garden_of_eden` (`✓ std3`). ∎

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

For every universe u, every A : Type(u) with Finite(A), every k : N and every local rule h, the original full code is surjective if and only if the original finite-difference preinjectivity predicate holds. The endpoint uses arbitrary integer configurations and equality of their complete code images. It has no periodic-domain restriction, finite-configuration restriction, alphabet lower bound, or supplied growth or balance condition.

If the code is surjective, every finite word occurs in its image, so actual prefix growth has rate log(card(A)). The strict image-prefix loss from a finite collision contradicts this rate. For the reverse direction, continuity of the native code on the compact finite-alphabet full shift makes its image closed. A point outside the image has a finite cylinder missing the image, and translation supplies a missing word at every site. A missing word of length m bounds the count at length nm by (card(A)^m−1)^n. Meanwhile preinjectivity makes the map from arbitrary source words of length n, inserted into a constant context, injective into image prefixes of length n+k+1. The resulting opposing growth bounds contradict one another. Empty and singleton alphabets are handled directly by subsingleton elimination.

This is the classical Moore–Myhill theorem specialized to the integer full shift. The collar replacement and entropy comparison follow the published Garden-of-Eden argument; the native proof reuses BipermutativeLift.code_shift, the original continuous_code theorem, and PrefixGrowthEntropy.prefix_growth_entropy.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/GardenOfEden.exists_erasable_words`
- Truth anchor: `D5/S1/Dynamics/Symbolic/GardenOfEden.garden_of_eden`
- Truth anchor: `D5/S1/Dynamics/Symbolic/GardenOfEden.imageRay`
- Truth anchor: `D5/S1/Dynamics/Symbolic/GardenOfEden.strict_image_prefix_loss`
- Truth anchor: `D5/S1/Dynamics/Symbolic/GardenOfEden.writeWord`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity](PermutativeLifts/BipermutativePreinjectivity.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy](PrefixGrowthEntropy.md)
