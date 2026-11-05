# Uniform Static Signature Code

## Abstract

A fixed alphabet encodes the truncated ancestor signature at every depth of the ordered address tree.

**Definition 1.1 (The alphabet size).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.alphabetSize`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.alphabetSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write N(0)=1 and N(h+1)=3 times 2 to the power h. The size depends only on the natural signature budget, independently of the address depth and its current colour.

**Definition 1.2 (Backward increment choices).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.Alphabet`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.Alphabet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-budget alphabet is Unit. At positive budget h+1 it is Fin 3 times the Boolean functions on Fin h. The three-valued coordinate records the incoming increment, ordered minus, zero, plus. For a child increment zero, the possible parent increments are minus and plus; for plus they are zero and plus; for minus they are minus and zero. False selects the smaller parent increment and true the larger. These are the backward rows of the fixed ordered child-increment table.

**Definition 1.3 (A symbol for every finite address).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.encode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At budget h+1, record the current incoming increment and h bits. Bit j records the backward choice from ancestor j to ancestor j+1 when j+1 is strictly smaller than the depth. Otherwise the bit is false. Thus the root uses a fixed symbol and short addresses pad every unused bit with false. No root incoming increment is requested as a backward choice. At budget zero use the unique Unit symbol.

**Theorem 1.4 (One alphabet decodes all depths).**

$$\forall m: \operatorname{Nat}, ((3 \le m) \implies (\forall h: \operatorname{Nat}, (\exists alpha: \operatorname{Address} \to \operatorname{Fin}\left(\operatorname{alphabetSize}\left(h\right)\right), (\exists D: ((\operatorname{ZMod}\left(m\right) \times \operatorname{Nat}) \times \operatorname{Fin}\left(\operatorname{alphabetSize}\left(h\right)\right)) \to (\operatorname{Nat} \times \operatorname{List}\left(\operatorname{ZMod}\left(m\right)\right)), (\forall p: \operatorname{Address}, (\operatorname{D}\left((\operatorname{observation}\left(m, p\right), \operatorname{alpha}\left(p\right))\right) = \operatorname{signature}\left(m, h, p\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.uniform_signature_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural modulus m at least three and every natural budget h, there exist a single map alpha from all finite literal addresses to Fin N(h) and a total function D from (ZMod m times Nat) times Fin N(h) to Nat times List (ZMod m), such that D(observation(m,p),alpha(p)) equals signature(m,h,p) for every address p. Both maps are chosen before the address is quantified. The observation supplies exactly the current colour and its unbounded natural depth.

The concrete symbol is encode transported along a finite equivalence to Fin N(h). Equal symbols give the same initial increment. At each further nonroot ancestor the corresponding equal bits and the backward table recover the same parent increment. Induction recovers all increments needed through min(h,depth). The incoming-colour identity then gives the next colour by subtracting that increment from the current colour. Induction therefore gives the entire original signature, including depth and the current colour.

The zero-budget signature follows from the observation alone. At every budget the root signature contains just its initial colour; at short addresses the colour list stops at the root. The proof covers arbitrarily large finite depths. Constancy of the signature on each combined observation-and-symbol fibre gives a total decoder by AnswerabilityCriterion.answerability_criterion; values on inputs outside the represented range are unrestricted.

This is the upper construction in finite joint cycle and radial prediction, Definition 3.1 and Theorem 3.2, with the ordered recursion of Continuation V, Definition 120.3. It is a static deterministic representation of the signature. It gives no lower bound or optimality assertion, and no procedure for acquiring a symbol, online workspace bound, sample bound, storage guarantee, or additional stochastic-law statement.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.Alphabet`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.alphabetSize`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.encode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.uniform_signature_code`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints](TrueJumpEndpoints.md)
