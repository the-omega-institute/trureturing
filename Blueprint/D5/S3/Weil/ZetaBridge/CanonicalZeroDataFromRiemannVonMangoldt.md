# Canonical `ZeroData` from Riemann–von Mangoldt

## Abstract

The repository already proves the exact characterization

\[
\operatorname{Nonempty}(\operatorname{ZeroData})
\iff
\{\rho\in\mathbb C:\operatorname{IsNontrivialZero}(\rho)\}
\text{ is infinite}.
\]

This node supplies the missing infinitude premise from the canonical set-level source `Zeta23.zetaZeroConfig` and Riemann–von Mangoldt count growth.

## Closed implication chain

For

\[
h_{\mathrm{RvM}}:
\operatorname{RiemannVonMangoldt}
  (\operatorname{zetaZeroConfig}),
\]

the node proves

\[
N(T,2T)\to\infty
\Longrightarrow
\operatorname{zetaZeroConfig.carrier}\text{ is infinite}
\Longrightarrow
\{\rho:\operatorname{IsNontrivialZero}(\rho)\}\text{ is infinite}
\Longrightarrow
\operatorname{Nonempty}(\operatorname{ZeroData}).
\]

It then defines an actual value

\[
\operatorname{zeroDataOfRiemannVonMangoldt}(h_{\mathrm{RvM}})
:
\operatorname{ZeroData}.
\]

## Library-first boundary

The node reuses `ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite`. Consequently it does not rebuild:

- the countable duplicate-free enumeration;
- exact analytic multiplicities;
- reflection and conjugation permutations;
- multiplicity invariance under both symmetries;
- compact spectral-ball finiteness.

Those obligations are already discharged in the equivalence theorem. This node only proves the canonical zero set is infinite under the explicit Riemann–von Mangoldt source and selects the resulting inhabitant.
