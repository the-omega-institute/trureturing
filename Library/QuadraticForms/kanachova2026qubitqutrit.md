---
bibkey: kanachova2026qubitqutrit
authors: Veronica Kanachova; Feng Liu; Zhoudunming Tu
year: 2026
title: "Qubit–Qutrit Quantum Tomography of hadronic Λφ and ΛK*0 systems"
doi: 10.48550/arXiv.2609.11151
url: https://arxiv.org/abs/2609.11151v1
claim: "Appendix §.7 conjectures that the fixed averaged reconstruction detects every pure entangled qubit-qutrit state; Eqs. (3), (S18) and (S19) specify the reconstruction and its local conjugation."
strata_touched:
  - D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2609.11151

Source: https://arxiv.org/abs/2609.11151v1

# Qubit–Qutrit Quantum Tomography

Veronica Kanachova, Feng Liu and Zhoudunming Tu, arXiv:2609.11151v1.
The state space is the complex qubit-qutrit tensor product. The ordered qutrit
basis is |+1⟩, |0⟩, |−1⟩.

Appendix §.7, printed p. 9, immediately after Proposition 1, states:

> We therefore \emph{conjecture}, without proof, that $\rho_{\rm meas}$ detects every pure entangled state of this system.

The main text, printed p. 2, defines the operational object:

> Let $\rho_{\rm meas}$ denote the density matrix obtained by setting the 23 measured parameters to their observed values and the inaccessible 12 to zero, which is the most complete reconstruction available from the decay angular distributions alone.

Equation (3), with Eqs. (S18)–(S19) on p. 9, gives

$$
\rho_{\rm meas}=\tfrac12[\rho+\mathcal U_B(\rho^{T_B})],\qquad
\mathcal U_B(\rho)=(1_2\otimes U)\rho(1_2\otimes U)^\dagger,\qquad
U=\begin{pmatrix}0&0&-1\\0&1&0\\-1&0&0\end{pmatrix}.
$$

The second-factor partial transpose has entry
$\rho^{T_B}_{(a,b),(a',b')}=\rho_{(a,b'),(a',b)}$.
Detection is expressed by a negative real eigenvalue with a nonzero eigenvector
of this fixed reconstruction. The quoted conjecture quantifies over both complex
Schmidt bases, beyond the restricted-basis calculation of Proposition 1.

The repository derivation uses the vector $(U\overline v,-U\overline u)$ for
the two rows $u,v$ of the input. Its expectation is minus the sum of the three
squared absolute minors. The conjecture is the source's statement; this
derivation is a repository result. Mixed-state detection, arbitrary symmetric
unitaries in higher dimensions and quantitative noise bounds remain outside
this result.

The exact symbolic and finite checks are in
the-omega-institute/trureturing-experiments, commit
`2e5c42249159964a68ca7ccf7bdf8d625d1afcad`,
`docs/reports/pure-state-detection/check.py`, sha256
`e594cec061c9a50e7f9eb615ecd80e2bbb04ae0d8f60e8da90bd18f636674261`.
The recorded command `python3 docs/reports/pure-state-detection/check.py`
exits 0 and reports `ALL_CHECKS_OK`. These checks supply computational evidence;
the universal result is the Lean theorem.

Literature-screen completeness is ASSUMED-UNVERIFIED. The inspected sources and
coverage limits are recorded in preregistration issue #22252; no exhaustive
novelty claim is made.
