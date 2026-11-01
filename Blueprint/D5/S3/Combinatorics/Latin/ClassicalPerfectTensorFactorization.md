# Classical perfect tensors have perfect factors

## Abstract

Every three-gate factorization of a classical six-leg perfect tensor has perfect two-wire factors.

**Definition 1.1 (Index-one orthogonal arrays).**

$$\forall \left(r: \operatorname{Type}_{v}\right), \left(\forall \left(x: \operatorname{Type}_{u}\right), \left([\operatorname{Fintype}\left(r\right)] [\operatorname{Fintype}\left(x\right)] , \left(\forall \left(c: \mathbb{N}\right), \left(\forall \left(rows: \left(r\right) \to \left(\left(\operatorname{Fin}\left(c\right)\right) \to \left(x\right)\right)\right), \left(\forall \left(s: \mathbb{N}\right), \left(\left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(rows, s\right)\right) \Leftrightarrow \left(\forall \left(cols: \left(\operatorname{Fin}\left(s\right)\right) \to \left(\operatorname{Fin}\left(c\right)\right)\right), \left(\left(\operatorname{Function.Injective}\left(cols\right)\right) \Rightarrow \left(\operatorname{Function.Bijective}\left(\lambda \left(t: r\right) \mapsto \left(\lambda \left(i: \operatorname{Fin}\left(s\right)\right) \mapsto \left(rows\left(t, cols\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.IsIndexOneOA` (`✓ std3`).

*Citation.* Balázs Pozsgay; Ian M. Wanless (2024). *Tensor network decompositions for absolutely maximally entangled states*. DOI: [10.22331/q-2024-05-08-1339](https://doi.org/10.22331/q-2024-05-08-1339). URL: <https://arxiv.org/abs/2308.07042v3>.

*Commentary.*

The row type r and symbol type x lie in independent arbitrary universes v and u; universe levels are implicit parameters throughout. For finite r and x, rows assigns one symbol to each row and column. Every ordered selection cols of s distinct columns must give a bijection from rows to s-tuples of symbols. Thus each tuple occurs exactly once. This is the orthogonality condition of factoringtriunit.tex, lines 891–902. The source also specifies the row count as the alphabet size to the power s; here that count follows whenever a selection of s distinct columns exists. If s exceeds c, there is no such selection and the predicate is vacuous.

**Definition 1.2 (The four-column graph of a gate).**

$$\forall \left(x: \operatorname{Type}_{u}\right), \left(\forall \left(f: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(t: \left(x\right) \times \left(x\right)\right), \left(\left(\operatorname{ClassicalPerfectTensorFactorization.gateGraph}\left(f, t\right): \left(\operatorname{Fin}\left(4\right)\right) \to \left(x\right)\right) = ![\left(t\right).1, \left(t\right).2, \left(f\left(t\right)\right).1, \left(f\left(t\right)\right).2]\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.gateGraph` (`✓ std3`).

*Citation.* Balázs Pozsgay; Ian M. Wanless (2024). *Tensor network decompositions for absolutely maximally entangled states*. DOI: [10.22331/q-2024-05-08-1339](https://doi.org/10.22331/q-2024-05-08-1339). URL: <https://arxiv.org/abs/2308.07042v3>.

*Commentary.*

A gate f sends two input symbols to two output symbols. Its graph records the inputs first, then the outputs, in columns numbered zero through three. This is the four-leg instance of the classical-map array in factoringtriunit.tex, lines 929–937, and the smaller arrays of lines 960–964. Perfection means that every pair of columns contains every ordered pair of symbols exactly once.

**Definition 1.3 (Three gates on three wires).**

$$\forall \left(x: \operatorname{Type}_{u}\right), \left(\forall \left(a: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(b: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(c: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(t: \left(x\right) \times \left(\left(x\right) \times \left(x\right)\right)\right), \left(\left(\operatorname{ClassicalPerfectTensorFactorization.circuit}\left(a, b, c, t\right): \left(x\right) \times \left(\left(x\right) \times \left(x\right)\right)\right) = \operatorname{let} \left(ab: \left(x\right) \times \left(x\right)\right) = a\left(\left(\left(t\right).1, \left(\left(t\right).2\right).1\right)\right); \left(\operatorname{let} \left(pc: \left(x\right) \times \left(x\right)\right) = b\left(\left(\left(ab\right).1, \left(\left(t\right).2\right).2\right)\right); \left(\operatorname{let} \left(qr: \left(x\right) \times \left(x\right)\right) = c\left(\left(\left(ab\right).2, \left(pc\right).2\right)\right); \left(\left(\left(pc\right).1, \left(\left(qr\right).1, \left(qr\right).2\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.circuit` (`✓ std3`).

*Citation.* Balázs Pozsgay; Ian M. Wanless (2024). *Tensor network decompositions for absolutely maximally entangled states*. DOI: [10.22331/q-2024-05-08-1339](https://doi.org/10.22331/q-2024-05-08-1339). URL: <https://arxiv.org/abs/2308.07042v3>.

*Commentary.*

The first gate a acts on wires one and two, producing ab. The second gate b acts on the first output of a and wire three, producing pc. The last gate c acts on the second output of a and the second output of b, producing qr. The final outputs are the first coordinate of pc and the two coordinates of qr. This is the order of composition in factoringtriunit.tex, lines 945–960, equation (4.2). Triples are pairs whose second coordinate is itself a pair.

**Definition 1.4 (The six-column circuit graph).**

$$\forall \left(x: \operatorname{Type}_{u}\right), \left(\forall \left(a: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(b: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(c: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(t: \left(x\right) \times \left(\left(x\right) \times \left(x\right)\right)\right), \left(\left(\operatorname{ClassicalPerfectTensorFactorization.circuitGraph}\left(a, b, c, t\right): \left(\operatorname{Fin}\left(6\right)\right) \to \left(x\right)\right) = ![\left(t\right).1, \left(\left(t\right).2\right).1, \left(\left(t\right).2\right).2, \left(\operatorname{ClassicalPerfectTensorFactorization.circuit}\left(a, b, c, t\right)\right).1, \left(\left(\operatorname{ClassicalPerfectTensorFactorization.circuit}\left(a, b, c, t\right)\right).2\right).1, \left(\left(\operatorname{ClassicalPerfectTensorFactorization.circuit}\left(a, b, c, t\right)\right).2\right).2]\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.circuitGraph` (`✓ std3`).

*Citation.* Balázs Pozsgay; Ian M. Wanless (2024). *Tensor network decompositions for absolutely maximally entangled states*. DOI: [10.22331/q-2024-05-08-1339](https://doi.org/10.22331/q-2024-05-08-1339). URL: <https://arxiv.org/abs/2308.07042v3>.

*Commentary.*

The six columns record the three inputs followed by the three circuit outputs. Rows are indexed by all input triples. This is the array associated with the classical map in factoringtriunit.tex, lines 929–937 and 945–955. Strength three says that any three distinct columns determine the input triple uniquely and attain every symbol triple.

**Definition 1.5 (Perfection descends to the three factors).**

$$\operatorname{ClassicalPerfectTensorFactorization.claim} = \left(\forall \left(x: \operatorname{Type}_{u}\right), \left([\operatorname{Fintype}\left(x\right)] , \left(\forall \left(a: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(b: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(c: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(\operatorname{ClassicalPerfectTensorFactorization.circuitGraph}\left(a, b, c\right), 3\right)\right) \Rightarrow \left(\left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(\operatorname{ClassicalPerfectTensorFactorization.gateGraph}\left(a\right), 2\right)\right) \land \left(\left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(\operatorname{ClassicalPerfectTensorFactorization.gateGraph}\left(b\right), 2\right)\right) \land \left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(\operatorname{ClassicalPerfectTensorFactorization.gateGraph}\left(c\right), 2\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Balázs Pozsgay; Ian M. Wanless (2024). *Tensor network decompositions for absolutely maximally entangled states*. DOI: [10.22331/q-2024-05-08-1339](https://doi.org/10.22331/q-2024-05-08-1339). URL: <https://arxiv.org/abs/2308.07042v3>.

*Commentary.*

For every finite alphabet x and arbitrary gates a, b and c, strength three of the circuit graph implies strength two of each gate graph. This formulates the nonlinear classical question in factoringtriunit.tex, lines 1196–1200, using the composition of equation (4.2). No linearity, field structure, initial bijectivity or dual unitarity is assumed for the factors. The statement includes empty alphabets. It asserts a property of any such factorization, without asserting that a factorization exists or that perfect factors always have a perfect composite.

**Theorem 1.6 (Every classical factor is perfect).**

$$\forall \left(x: \operatorname{Type}_{u}\right), \left([\operatorname{Fintype}\left(x\right)] , \left(\forall \left(a: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(b: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\forall \left(c: \left(\left(x\right) \times \left(x\right)\right) \to \left(\left(x\right) \times \left(x\right)\right)\right), \left(\left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(\operatorname{ClassicalPerfectTensorFactorization.circuitGraph}\left(a, b, c\right), 3\right)\right) \Rightarrow \left(\left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(\operatorname{ClassicalPerfectTensorFactorization.gateGraph}\left(a\right), 2\right)\right) \land \left(\left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(\operatorname{ClassicalPerfectTensorFactorization.gateGraph}\left(b\right), 2\right)\right) \land \left(\operatorname{ClassicalPerfectTensorFactorization.IsIndexOneOA}\left(\operatorname{ClassicalPerfectTensorFactorization.gateGraph}\left(c\right), 2\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.result` (`✓ std3`). ∎

*Resolves.* `Problems/pozsgay-wanless-2024-nonlinear-perfect-tensor-factors` (proved) by `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pozsgay-wanless-2024-nonlinear-perfect-tensor-factors","declaration_gid":"D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Balázs Pozsgay; Ian M. Wanless (2024). *Tensor network decompositions for absolutely maximally entangled states*. DOI: [10.22331/q-2024-05-08-1339](https://doi.org/10.22331/q-2024-05-08-1339). URL: <https://arxiv.org/abs/2308.07042v3>.

*Commentary.*

For any three distinct columns, equality of their entries forces equality of rows, and every prescribed triple of entries occurs. A two-wire gate is perfect if it is bijective and each output coordinate is bijective in each input separately. Indeed, two input columns determine the input directly; one input and one output use the corresponding one-variable bijection; two output columns use bijectivity of the gate. These give injectivity for every two-column projection. Composing with the equivalence between functions on Fin 2 and pairs turns each projection into a self-map of the finite pair type, so injectivity gives bijectivity.

First suppose x is nonempty, and denote the input and output symbols by (x,y,z) and (p,q,r). Write a₁,a₂ and b₁,b₂ for the gate coordinates, and write c₁,c₂ for the last gate coordinates. The lifted gates on triples are (x,y,z) ↦ (a₁(x,y),a₂(x,y),z), (u,v,z) ↦ (b₁(u,z),v,b₂(u,z)), and (p,v,w) ↦ (p,c₁(v,w),c₂(v,w)). Their composite is injective by the output columns (p,q,r), hence bijective on the finite triple type. Injectivity of the composite makes the first lifted gate injective, hence bijective. Cancelling it gives a bijective composite of the other two; the same argument makes the second and then the third lifted gate bijective. Reassociation and interchange of coordinates identify these lifts with products of a, b or c and an identity map. Nonemptiness then gives bijectivity of a, b and c.

Choose a fixed symbol d. For fixed y, equal values of a₁(s,y) and a₁(t,y) give equal p values with z = d; columns (y,z,p) force s = t. For fixed x, columns (x,z,p) similarly give injectivity of y ↦ a₁(x,y). Finiteness makes both families bijective. For fixed z, lift two proposed inputs of b₁ through the bijection x ↦ a₁(x,d). Equal b₁ outputs then give equal circuit rows by (y,z,p), so the proposed inputs coincide. For fixed first input of b₁, choose an a-preimage with that first output using bijectivity of a. Equal values as z varies give equal rows by (x,y,p). Thus b₁ is also bijective in each input.

Next fix y and a desired value v of a₂. Surjectivity on columns (y,q,r) produces a row with these last two entries equal to c(v,d). Injectivity of c forces the second output of a to be v. Columns (x,q,r) give the same surjectivity with x fixed. Finiteness makes both one-variable maps for a₂ bijective. To treat the first argument of b₂ with z fixed, choose a-preimages of (u,d) and (v,d). If b₂(u,z) = b₂(v,z), their last two circuit outputs are equal, so columns (z,q,r) identify the rows and give u = v. For the second argument of b₂ with first argument v fixed, choose u with a₁(u,d) = v. Equal values b₂(v,s) and b₂(v,t) give equal q and r with y = d; columns (y,q,r) force s = t. Finiteness again upgrades injectivity to bijectivity.

For the first coordinate of the last gate, fix its second input v. Choose w with b₂(w,d) = v, and a-preimages of (w,s) and (w,t). The associated circuit rows have the same z = d and the same p. Equality of c₁(s,v) and c₁(t,v) then lets columns (z,p,q) identify those rows, giving s = t. To fix the first input v, choose an a-preimage of (d,v), then choose inputs of the bijection z ↦ b₂(d,z) realizing any proposed pair s,t. Equality of c₁(v,s) and c₁(v,t) gives equal rows by (x,y,q), so s = t. Thus c₁ is bijective in each input by finiteness.

For c₂ with second input v fixed, again choose w with b₂(w,d) = v and a-preimages of (w,s) and (w,t). The resulting rows have equal z and p; if c₂(s,v) = c₂(t,v), columns (z,p,r) identify the rows and force s = t. With first input v fixed, choose an a-preimage of (d,v), and use the bijection z ↦ b₂(d,z) to realize s and t. Equality of c₂(v,s) and c₂(v,t) then identifies the rows by (x,y,r), again forcing s = t. Finiteness makes both one-variable maps bijective.

The two-column criterion now applies to a, b and c, since each gate is bijective and both its coordinates are bijective in either input. This proves the three required strength-two properties. If x is empty, the row type x × x and the target type Fin 2 → x are both empty, so every two-column projection is bijective. This gives the same conclusion in the remaining case.

## References

- Truth anchor: `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.IsIndexOneOA`
- Truth anchor: `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.circuit`
- Truth anchor: `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.circuitGraph`
- Truth anchor: `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.claim`
- Truth anchor: `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.gateGraph`
- Truth anchor: `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.result`
