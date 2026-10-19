---
bibkey: cramer1922mittelwert
authors: Harald Cramér
year: 1922
title: Ein Mittelwertsatz in der Primzahltheorie
doi: 10.1007/BF01482072
url: https://doi.org/10.1007/BF01482072
claim: Under RH, the introductory square-mean estimate bounds the integral of (psi(t)-t)^2/t by O(X); it supplies the conditional direction of the critical-energy application.
strata_touched: []
license: citation-only
triage: anchor
---

# The conditional square mean of the prime-counting error

The source is *Mathematische Zeitschrift* 12 (1922), 147–153.
Crossref identifies the title, author, volume, pages and DOI.
The [GDZ primary scan](https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0012/LOG_0013.pdf)
contains eight PDF pages including a terms cover; printed p.147 is PDF
page 2. No source pages or images are vendored here.

At the beginning of printed p.147, the standing italic hypothesis says
that RH is assumed in the first three numbered sections. The same page
defines $\psi(x)=\sum_{p^m\le x}\log p$ and gives the unnumbered
introductory estimate

$$
\frac1X\int_2^X\left(\frac{\psi(t)-t}{\sqrt t}\right)^2dt=O(1),
\qquad X\longrightarrow\infty.
$$

The author attributes this square-mean result to his *Some theorems
concerning prime numbers*, *Arkiv för Matematik* 15, no.5 (1920).
The input used here is the explicit 1922 restatement with its RH premise;
the classical estimate is cited, not reproved. Inspection establishes its
stated normalization and hypothesis, not a Lean formalization or an
independent rerun of the source proof.

Writing $M(X)=\int_2^X(\psi(t)-t)^2/t\,dt$, the exact input is
$M(X)=O(X)$ under RH. The
[centered primary-prime application](../../Zeros/coffey2009stieltjes.md#cs7-the-critical-primary-prime-energy-is-an-rh-level-premise)
uses it on dyadic intervals to identify the strength of a proposed
Laguerre energy assumption. It is not an unconditional budget for that
energy or a new estimate for the original signed joint matrix.
