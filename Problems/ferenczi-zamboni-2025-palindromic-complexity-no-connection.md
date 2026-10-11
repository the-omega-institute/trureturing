---
slug: ferenczi-zamboni-2025-palindromic-complexity-no-connection
bibkey: ferenczizamboni2025clustering
doi: null
url: https://arxiv.org/abs/2507.17370v2
triage: theorem
motivation_gids:
  - D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.result
---

# Symmetric Order and No Connections Do Not Force Full Palindromic Complexity

## Problem

Sébastien Ferenczi and Luca Q. Zamboni, *Clustering, order conditions, and languages of interval exchanges*, arXiv:2507.17370v2, Section 4, Conjecture 1, page 14:

> A language on $k$ letters satisfying a symmetric order condition and with no connection has palindromic complexity $1$ for $n$ even, $k$ for $n$ odd.

The source language is factorial and two-sided extendable. A symmetric pair has arrival order opposite to departure order. Connections are the consecutive-letter, missing-cross-edge configurations of Definition 7. Recurrence and closure under reversal are not hypotheses of this conjecture. Preregistration: [#15331](https://github.com/the-omega-institute/trureturing/issues/15331).

## Motivation

`D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.result` refutes the universally quantified conjecture with a four-letter language and length three. The module uses `Fin 4` values $0,1,2,3$ for the source vertices $1,2,3,4$.

## Gap

The bounded literature screen in #15331 inspects both versions of the source, its related papers and classical references, MathDB, and the repository. No settlement was found in that searched scope. This negative finding does not establish that no uninspected publication exists.

## Route

Use all finite paths, including the empty path, in the graph with edges $0\to3$, $1\to3$, $2\to j$ for every $j$, and $3\to0$. The departure order is numerical and the arrival order is its reverse.

The private declarations `factorial`, `extendable` and `usesAll` establish the three language axioms; `symOrder` establishes the symmetric order condition; `only_empty_bispecial` and `noConnection` establish absence of connections. `pal_set` identifies exactly the three length-three palindromes $[2,2,2]$, $[0,3,0]$, $[3,0,3]$, and `pal3` establishes $PC(3)=3$. Instantiating the conjecture at $k=4,n=3$ would give $PC(3)=4$.

Source-faithfulness remark: for a nonempty source alphabet, `IsFactorial` and `UsesAllLetters` imply the source's separate empty-word requirement. Choose any letter; its singleton is in the language, and the empty word is an infix of that singleton. In this refutation the alphabet has four letters. This remark introduces no Lean declaration.

## Falsifier

A transcription mismatch in any language axiom, order comparison, connection configuration, or palindrome count would invalidate the settlement. The decisive exact check is that the four-letter path language satisfies all five hypotheses while $PC(3)=3\ne4$.

## Evidence

The settling theorem is `result : ¬ claim`; its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. Only $k=4$ is formalized.

Experiment entry: [docs/reports/ferenczi-zamboni-2025-palindromic-complexity-no-connection](https://github.com/the-omega-institute/trureturing-experiments/tree/737aba5255513d181c03cb983b6bc6172d1c3705/docs/reports/ferenczi-zamboni-2025-palindromic-complexity-no-connection), specifically `check.py` at commit `737aba5255513d181c03cb983b6bc6172d1c3705`. Command in that directory: `python3 check.py`; exit 0; script SHA-256 `043ab7f7e1b47440906bf43f1812195d649eb2ef5ba8587596a10668de0b5812`; final reading `bad= 0`.

The exhaustive scope is $k=4,5,6,7,8$ and word lengths $0\le n\le12$; the order-condition test covers every middle word with $|x|\le10$. Within that scope the program verifies factoriality, two-sided extendability, all letters, the symmetric order condition, the empty word as the only bispecial, absence of its connections, $p(n)=(k-1)n+1$, and $PC=(1,k,1,3,1,3,\ldots)$. No experiment program or data is embedded here.

## Triage

### What the settlement shows

- **Mechanism — proved by the mathematical argument below; the four-letter decisive instance is kernel-checked.** For $k\ge4$, write $c=k-1,d=k$ in the source's one-based alphabet. The graph has edges $i\to d$ for $1\le i\le k-2$, $c\to j$ for every $j$, and $d\to1$. In a palindrome, reflecting any adjacent pair supplies the reverse edge. Its only reciprocal edges are $c\to c$ and $1\leftrightarrow d$. A word of length at least two using only reciprocal edges therefore lies entirely in the loop or entirely in the two-cycle. Thus the transient letters $2,\ldots,k-2$ occur in the alphabet and in factors, but never in such palindromes. The loop gives $c^n$; the two-cycle gives two alternating palindromes exactly when $n$ is odd. Hence $PC(2m)=1$ for $m\ge1$ and $PC(2m+1)=3<k$ for $m\ge1$. These all-length statements are a mathematical argument, not additional Lean theorems.

  Only $1,d$ have several predecessors, while only $c$ has several successors. A nonempty left-special path must start at $1$ or $d$ and then remain in their two-cycle; a right-special path must end at $c$. Both conditions cannot hold together. At the empty word the successor rows, in numerical order, are $\{d\},\ldots,\{d\},\{1,\ldots,k\},\{1\}$. Distinct tails and heads reverse numerical order. An adjacent pair meeting the universal row has a cross edge, and other adjacent rows either have the same singleton successor or meet that universal row. This establishes the general structural mechanism in the argument in this dossier. For $k=4$, `only_empty_bispecial`, `symOrder`, `noConnection`, `pal_set` and `pal3` are kernel-checked declarations used by `result`.

  The language is not closed under reversal: $2d$ occurs but $d2$ does not. It is not generated by one infinite or bi-infinite word: every transient letter has only $c$ as predecessor, so it can occur at most once on a single path, whereas $c^r2$ occurs for every $r$. A one-sided path has only finitely many positions before that occurrence; a bi-infinite path containing it has no occurrence of $c1$, which also belongs to the language. The source's stronger equality proposition assumes generation by an infinite or bi-infinite word together with reversal closure and no connections; this witness does not satisfy those additional hypotheses.

- **Family — computed.** The pinned experiment checks $L_k$ for $k=4,\ldots,8$ through length 12, with $p(n)=(k-1)n+1$ and $PC=(1,k,1,3,1,3,\ldots)$. Evidence: the experiment entry, command, exit and SHA-256 above. Only the four-letter refutation is kernel-checked. A uniform Lean theorem for every $k\ge4$, including the factor-complexity formula, is open.

- **What survives — proved by the source.** Proposition 14, Section 4, page 13 of arXiv:2507.17370v2 gives $PC(n)\le1$ for even $n$ and $PC(n)\le k$ for odd $n$ under the symmetric order condition. Its equality conclusion also assumes generation by an infinite or bi-infinite word, closure under reversal and absence of connections. The refutation preserves these bounds and does not refute that stronger result. No source result established using the stronger hypotheses is invalidated by this witness; no additional downstream consequence is certified here.

- **Readings — computed.** The sole experiment entry is the pinned `check.py` named in Evidence, with precisely the finite tested scope and readings stated there.

- **Small alphabets — open.** Whether the conjecture holds for $k\le3$ in the source's nonempty-alphabet domain is unresolved here.

- **Recurrence — open.** Whether adding recurrence without closure under reversal restores equality is unresolved here.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). There are no other public theorems in this module.

## ASSUMED-UNVERIFIED

The literature conclusion is limited to the screen recorded in #15331. The finite experiment is not a kernel proof for every $k$ or every length. The general mechanism above is an argument in this dossier; Lean certifies the four-letter, length-three settlement and its required private predicates. The small-alphabet and recurrence questions remain open.
