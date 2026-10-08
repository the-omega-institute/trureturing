---
slug: teimoori-faal-2026-b-restricted-clique-real-stability
bibkey: teimoorifaal2026brestricted
doi: null
url: https://arxiv.org/abs/2602.24151v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.result
---

# Faal's Open Problem 1: non-chordal graphs with unstable restricted clique polynomials

## Problem

H. Teimoori Faal, *A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion*, arXiv:2602.24151v1, Section 7, Open Problem 1, asks:

> Necessity of Conditions: Are the conditions of r-connectivity and chordality also necessary? Is there an r-connected K_{r+3}-free non-chordal graph for which C_B(G;x,y) fails to be real-stable?

The second question has a positive answer for every integer $r\geq1$. The polynomial is the literal clique sum

$$C_B(G;x,y)=\sum_{K\subseteq V(G),\ K\text{ clique}}x^{|K|}y^{|K\cap B|},$$

including the empty clique. Real stability means that the polynomial is not identically zero and has no zero with $\operatorname{Im}(x)>0$ and $\operatorname{Im}(y)>0$.

## Motivation

The declaration `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.result` supplies a family at every positive connectivity, with an explicit upper-half-plane zero. It separates the existence question from the source's proposed chordal stability theorem.

## Gap

[Preregistration #14258](https://github.com/the-omega-institute/trureturing/issues/14258) records this tier-1 published question, the literal source, the fully quantified family, the Lean conventions, and bounded arXiv, OpenAlex, MathDB and repository literature checks. No settlement was found in those checked scopes. No exhaustive publication-priority claim is made.

## Route

Put $a=\max(r-2,0)$, $G_r=K_a\vee C_4$, and $B=\{v_0\}$, with $v_0$ a cycle vertex. Cliques of a join split into cliques of the two factors, and

$$C_B(G_r;x,y)=(1+x)^a(1+2x)(1+x+xy).$$

The last factor vanishes at $(x,y)=(i,-1+i)$, whose two imaginary parts equal $1$. A remaining complete-graph vertex connects every surviving vertex after deletion. If all complete-graph vertices are deleted, fewer than $a+2$ total deletions remove at most one cycle vertex, and the remaining cycle is connected. This proves the required $r$-connectivity. Every clique has size at most $a+2<r+3$, and the cycle vertices induce a chordless four-cycle. For $r=1$ and $r=2$, $G_r=C_4$; the assertion concerns $r$-connectivity and makes no exact-connectivity claim.

## Falsifier

A failure of any one of the four claimed properties for any $r\geq1$ would contradict FAAL-1. Source fidelity requires vertex deletion connectivity, literal cycle-and-chord chordality, Mathlib clique-freeness, and the literal clique polynomial rather than a substitute certificate predicate.

## Evidence

The frozen public theorem `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.result : claim` quantifies every natural $r\geq1$ and supplies a finite graph and marked set satisfying all four properties. Its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The corresponding Scribe resolution is Proved.

The kernel-checked private declarations `C_B_join`, `C4_factor`, `family_factor`, `family_zero`, `family_connected`, `family_cliqueFree`, and `family_nonchordal` are on the settling theorem's live dependency path. The claim and every public definition have canonical Scribe formulas.

## Triage

### What the settlement shows

- **Proved — kernel-checked declarations:** the decisive mechanism is the factor $1+x+xy$ of the marked $C_4$. The identity $C_B(C_4;x,y)=(1+2x)(1+x+xy)$ is `C4_factor`; join multiplication is `C_B_join`; the full family identity is `family_factor`; and its zero is `family_zero`. These establish the mechanism for every $a\geq0$ and the existence settlement for every $r\geq1$.
- **Proved — paper argument, not a Lean declaration in this module:** source Theorem 4.8 fails already on $K_{r+1}$ with $B=V$ for every $r\geq1$. The graph is $r$-connected: deleting fewer than $r$ vertices leaves a complete graph on at least two vertices. It is chordal and $K_{r+3}$-free. Every vertex is marked, so the binomial theorem gives $C_B(K_{r+1};x,y)=(1+xy)^{r+1}$. At $x=y=i$, both imaginary parts equal $1$, while $xy=-1$ and the polynomial vanishes. Thus the source's claimed sufficiency theorem is false, and the necessity question loses that premise. This argument uses no assertion of Theorem 4.8 as a dependency of the settlement. Any source conclusion relying on its universal stability assertion requires an independent proof or repaired hypotheses.
- **Open — literature question:** which marked subsets $B$ preserve real stability of $C_B$ remains unresolved by this delivery. A classification, including the $B=\varnothing$ triangle-free regime mentioned in #14258, is a follow-up question. The single marked cycle vertex supplies an unstable family and does not provide such a classification.

## ASSUMED-UNVERIFIED

Absence of a prior settlement outside the bounded literature scopes recorded in #14258 is unverified. The Theorem 4.8 counterexample above is a paper proof; no separate kernel-checked theorem for it is delivered. Information-escape registration is paused under CLAUDE.md section 3.9.
