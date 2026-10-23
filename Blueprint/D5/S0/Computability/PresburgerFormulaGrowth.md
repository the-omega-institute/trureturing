# Original Presburger Formula Growth

## Abstract

The original integer QF syntax has a separated-atom Growth derivation at a fixed source prefix.

Use the executable Affine, Atom and QF syntax from ProveIt at ec9ab2ffd49f8861022d6f3d4c30205545a3386d, retained by the supplier under MIT-0. No alternate quantifier elimination or semilinear framework is introduced. The source and descriptor carriers may be arbitrary types. A source valuation has a fixed length m; a descriptor valuation is an arbitrary suffix. The original dot product truncates to the shorter list.

**Theorem 1.1 (Structural derivation from actual affine atoms).**

$$\operatorname{Growth}\left(QFevaluation, modulusProduct, thresholdCount\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerFormulaGrowth.qf_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original QF p, every natural m, sourceEnv:X->List Int and suffixEnv:Y->List Int with length(sourceEnv(x))=m for all x, the relation p.eval(sourceEnv(x)++suffixEnv(y)) has Growth with the budget of p. Constants have budget (1,0), nonnegative affine atoms (1,1), positive-modulus dvd and ndvd atoms (d,0). Not preserves budget; and/or multiply coefficients and add exponents.

The live dot_append lemma proves dot(a,xs++ys)=dot(take(length(xs),a),xs)+dot(drop(length(xs),a),ys) by induction, including empty and short coefficient lists. Thus an affine term is A(x)+B(y), with A=dot(take(m,coeffs),sourceEnv(x)) and B=constant+dot(drop(m,coeffs),suffixEnv(y)). Its nonnegative atom is the threshold -A<=B, while its divisibility atoms use Growth.dvd or Growth.ndvd with the original positive natural modulus. QF induction constructs constant, unary and binary Growth proofs. It does not assume a polynomial bound or define Presburger semantics to be Growth. Negative integer coefficients, zero prefix length and empty carriers are included.

The reusable contribution is the exact environment separation and its derivation over the supplier syntax. The polynomial trace bounds themselves are reused from PresburgerPatternGrowth; the general tame-growth phenomenon is established literature (Aschenbrenner et al., VC density I). No claim of a new quantifier-elimination algorithm or general NIP theorem is made.

## References

- Truth anchor: `D5/S0/Computability/PresburgerFormulaGrowth.qf_growth`
- Dependency: [D5/S0/Computability/PresburgerPatternGrowth](PresburgerPatternGrowth.md)
- Dependency: [D5/S0/Computability/PresburgerSyntax](PresburgerSyntax.md)
