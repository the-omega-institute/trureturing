# The Fifth-Iterate Exponential Pattern Modulo Three

## Abstract

From index three, the coefficients of OEIS A396805 have repeating residues 0, 1, 0 modulo three.

Let A be the unique rational formal series with zero constant coefficient satisfying A=X*exp(A^{[5]}), where A^{[5]} is the fifth compositional iterate. Write a(n)=n![X^n]A. The existing A_equation and fixed_unique in IterateExponentialParity identify A with AK(5) and a(n) with aK(5,n). In the formula, ite(p,x,y) equals x when p holds and y otherwise.

**Theorem 1.1 (Hanna's pattern from index three).**

$$\forall n:\mathbb{N}, 3\leq n\implies \operatorname{aK}\left(5, n\right) \bmod 3=\operatorname{ite}\left(n \bmod 3=1, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialFiveModThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396805-iterate-exponential-mod-three` (proved) by `D5/S1/Recurrence/Residue/IterateExponentialFiveModThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396805-iterate-exponential-mod-three","declaration_gid":"D5/S1/Recurrence/Residue/IterateExponentialFiveModThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396805: iterated-exponential congruences at iterate count 5*. URL: <https://oeis.org/A396805>.

*Commentary.*

The residue is one precisely at indices congruent to one modulo three and zero at the other indices in the domain n>=3. This is the source pattern 0, 1, 0 starting at n=3. The source value a(2)=2 explains why that lower bound must be retained. The earlier parity result and the separately recorded non-kernel modulo-five counterexamples have their own evidence; this theorem resolves only the modulo-three clause.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialFiveModThree.result`
- Dependency: [D5/S1/Recurrence/Residue/IterateExponentialParity](IterateExponentialParity.md)
