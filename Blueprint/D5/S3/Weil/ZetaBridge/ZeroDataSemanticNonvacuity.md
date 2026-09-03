# Semantic Nonvacuity for `ZeroData`

## Abstract

Every supplied `ZeroData` value is indexed by `ℕ`, so it already contains a zeroth represented zero. The semantic-vacuity risk lies one level higher. The type `ZeroData` may have no inhabitant, allowing a proposition of the form

\[
\forall Z:\operatorname{ZeroData},\;P(Z)
\]

to hold without being instantiated on any zeta-zero enumeration.

This node formalizes the distinction between a universal conditional claim and a realized claim

\[
\operatorname{RealizedZeroDataClaim}(P)
:\Longleftrightarrow
\exists Z:\operatorname{ZeroData},\;P(Z).
\]

## Main declarations

- `RealizedZeroDataClaim`
- `ZeroData.exists_nontrivial_zero`
- `forall_zeroData_of_not_nonempty`
- `realized_of_forall_of_nonempty`
- `realized_of_forall_of_riemannVonMangoldt`
- `exists_nontrivial_zero_of_riemannVonMangoldt`
- `realized_claim_with_nontrivial_zero`

## Exact logical boundary

The node proves

\[
\neg\operatorname{Nonempty}(\operatorname{ZeroData})
\Longrightarrow
\forall Z:\operatorname{ZeroData},\;P(Z),
\]

and

\[
\operatorname{Nonempty}(\operatorname{ZeroData})
\land
\bigl(\forall Z,\;P(Z)\bigr)
\Longrightarrow
\exists Z,\;P(Z).
\]

For the canonical zeta configuration, Riemann--von Mangoldt growth supplies the required nonemptiness. The resulting realizing enumeration also exhibits a genuine nontrivial zeta zero through its zeroth entry.

The node makes no RH claim. Its purpose is to prevent a theorem over all `ZeroData` values from being reported as a semantically instantiated zeta theorem until an actual inhabitant is available.
