---
bibkey: zhu2026uniformly
authors: X. Zhu; Y. Wang
year: 2026
title: "Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark"
doi: 10.48550/arXiv.2608.11850
url: https://arxiv.org/abs/2608.11850v1
claim: "A uniformly stable finite-field construction in characteristic three remains open: a family of fiducials phi_q in C^{F_q}, q = 3^r, whose Weyl-Heisenberg projector Gram matrices have SIC-normalized smallest nonidentity eigenvalue eta(phi_q) bounded below by a positive constant independent of q."
strata_touched:
  - D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability
license: citation-only
triage: anchor
---

# Uniformly stable minimal Weyl–Heisenberg measurements

X. Zhu and Y. Wang, arXiv:2608.11850v1 (2026-08-12), quant-ph; only v1 exists.
Source file `main_final.tex`. Sections are numbered by the order of `\section`
commands: the finite-field constructions are Section IV, the Discussion is Section VI.

The open item, verbatim. Section IV.B (*A flat profile with a zero axis*):

> This cubic mechanism excludes characteristics two and three; characteristic two is handled separately by Theorem~\ref{thm:char-two}, while a uniformly stable finite-field construction in characteristic three remains open.

Section VI (*Discussion*):

> A uniformly stable finite-field construction in characteristic three remains open.

The definitions, verbatim. Eq. (3):

> \eta(\phi)=\frac{d+1}{d}\lambda(\phi) =(d+1)\min_{u\ne0}\abs{\bra\phi D_u\ket\phi}^2.

Section II.A:

> \lambda(\phi) :=\lambda_{\min}\!\left( G_\phi^\Pi\big|_{\boldsymbol{1}^{\perp}} \right) \label{eq:lambda-definition} \end{equation} is its smallest nonidentity eigenvalue, including zero when the orbit is incomplete.

Section II.B:

> \inf_{d\in\mathcal D}\eta(\phi_d)>0 \label{eq:uniform-stability} \end{equation} \emph{uniform spectral stability}.

Section IV (finite-field Weyl–Heisenberg orbit):

> \psi(x)=\exp\!\left[\frac{2\pi i}{p} \Tr_{\F_q/\F_p}(x)\right] \label{eq:additive-character} \end{equation} be its canonical additive character.

> X_a\ket x=\ket{x+a}, \qquad Z_b\ket x=\psi(bx)\ket x, \qquad a,b\in\F_q.

> Set \(D_{a,b}=X_aZ_b\), \( \Pi_{a,b}=D_{a,b}\ketbra\phi\phi D_{a,b}^\dagger \), and \(E_{a,b}=\Pi_{a,b}/q\).

> G_\phi^\Pi[(a,b),(c,e)] =\Tr(\Pi_{a,b}\Pi_{c,e}),

The characteristic-two family of Section IV.A, Eq. `eq:char-two-state`, is
$\ket{\phi_{q,\theta}}=(\ket{+_q}+e^{i\theta}\ket0)/\sqrt{N_{q,\theta}}$ with
$N_{q,\theta}=2+2\cos\theta/\sqrt q$, used there at $\theta_q\ne0$ for $q=2^m$
(Theorem `thm:char-two`); the characteristic $p\ge5$ family is the balanced
Alltop construction of Sections IV.C–D.

## Verified locator

DOI: `10.48550/arXiv.2608.11850`. Canonical source URL: `https://arxiv.org/abs/2608.11850v1`.
The open item is in Sections IV.B and VI; η is Eq. (3); λ is `eq:lambda-definition`;
uniform spectral stability is `eq:uniform-stability`; the field Weyl–Heisenberg
operators and the projector Gram matrix are `eq:additive-character`, `eq:field-WH` and
`eq:field-projector-Gram`.
