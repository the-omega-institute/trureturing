---
bibkey: pauwelsguhne2026measurementbases
authors: Jef Pauwels; Otfried Gühne
year: 2026
title: "The Entanglement Content of Quantum Measurement Bases"
doi: null
url: https://arxiv.org/abs/2608.21185v1
claim: "Four-qubit marginal entropy: the Higuchi–Sudbery candidate, its known restrictions, and the unrestricted maximum question. Section VI asks for characterizations of further encoding classes, among them commuting families whose local factors are not Hermitian."
strata_touched:
  - D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum
  - D5/S3/Quantum/Information/CommutingEncodingReflectionClass
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2608.21185v1

# The Entanglement Content of Quantum Measurement Bases

## Status of global optimality

Section IV, p. 8:

> Higuchi and Sudbery originally proposed it using the corresponding average von Neumann entropy; it is a proven local maximum and a global maximum within the 1-uniform family for that functional, while unrestricted global optimality remains conjectural [34, 36, 46].

The preceding sentences distinguish this functional from two established maxima:

> The example is independently notable for its entanglement. It globally maximizes both the geometric measure [35, 45] and the average two-versus-two linear entropy [36].

The displayed state has $\omega=e^{2\pi i/3}$ and the same six occupied computational basis strings as the original Higuchi–Sudbery candidate. This note attests the published open status of the unrestricted average von Neumann entropy question; it supplies no proof of the entropy bound.

## Local encodings and the open question

Local encodings (l. 328–340):

> \begin{definition}[Local encoding]\label{def:local-encoding}
> A \emph{local encoding} of a fiducial state $\ket\psi$ is a family of
> product unitaries
> \[
>   U_a=\bigotimes_{j=1}^n U_{a,j},
>   \qquad a=1,\ldots,N,
> \]
> such that
> \begin{equation}\label{eq:encoding-condition}
>   \langle\psi|U_a^\dagger U_b|\psi\rangle=\delta_{ab}.
> \end{equation}
> A state that admits such a family is \emph{locally encodable}.
> \end{definition}

Encoder structures (l. 357–368):

> \begin{definition}[Encoder structures]\label{def:encoder-structures}
> An encoding is
> \begin{enumerate}[label=(\roman*)]
>   \item \emph{independent} if its labels are bit strings
>   $a=(a_1,\ldots,a_n)$ and
>   $U_a=\bigotimes_j U_j(a_j)$: party $j$ uses only the private bit $a_j$;
>   \item \emph{commuting-reflection} if the $U_a$ commute pairwise and every
>   local factor $U_{a,j}$ is a Hermitian unitary involution,
>   $U_{a,j}^\dagger=U_{a,j}$ and $U_{a,j}^2=\openone$;
>   \item \emph{general} if no restriction beyond product unitarity is imposed.
> \end{enumerate}
> \end{definition}

The open question of Section VI (l. 1539–1546):

> raises what we consider the central open question.  \emph{Which other
> encoding classes define natural state classes, and what do these sets look
> like?}  Concrete intermediate classes could be: coordinated
> tables of Pauli operators that need not commute, as in the $W$-basis of
> Miyake and Briegel \cite{Miyake2005}; commuting families whose local factors
> are not Hermitian, the smallest step beyond our theorem; and tables of local
> Clifford unitaries, as in our $M_4$ construction.  For none of these is a
> characterization known, although $M_4$ now proves that the last class is

Source TeX `main.tex`, md5 `217f1dae7e17966b2c9016fa75ef756b`: local encodings, l. 328–340; encoder structures, l. 357–384; the characterization of commuting-reflection encodings, l. 542–560; the open question, l. 1539–1546.
