---
slug: mandal-manna-dq-dilworth
bibkey: mandalmanna2026distance
doi: 10.48550/arXiv.2610.08599
url: https://arxiv.org/abs/2610.08599v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.result
---

# Refutation of Mandal–Manna Conjecture 5.5

## Problem

Mandal and Manna, *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*, arXiv:2610.08599v1, Conjecture 5.5:

> For every connected $\mathcal{C}$-graph $G$, every eigenvalue of $D^Q(G)$ not in $\mathcal{T}^Q(G)$ satisfies $\operatorname{mult}_{D^Q(G)}(\theta) \le \nabla(G)$.

The source defines $C(\alpha_1)=\overline{K_{\alpha_1}}$ and $C(\alpha_1,\ldots,\alpha_i)=\overline{C(\alpha_1,\ldots,\alpha_{i-1})\cup K_{\alpha_i}}$ for $i\ge2$, with positive block sizes and even sequence length. It defines $D^Q(G)=\operatorname{Tr}(G)+D(G)$, the vicinal preorder, and the local set $\mathcal{T}^Q(G)$.

## Motivation

The frozen result supplies a concrete connected source graph whose distance-signless matrix has a nonlocal repeated eigenvalue while its vicinal cover number is one. This tests the universal multiplicity bound in the exact source domain.

## Gap

Issue #23915 recorded the source statement, the counterexample construction, exact finite checks, and a bounded literature screen. No settlement was found in the inspected sources. Literature-search completeness is `ASSUMED-UNVERIFIED` because citation providers were rate-limited and several older full texts were unavailable.

## Route

The Lean module formalizes the recurrence, native graph distance, transmission, distance-signless matrix, local exceptions, vicinal chain covers, and algebraic multiplicity. For the eight-vertex instance $\alpha=(1,1,1,1,1,1,1,1)$, it proves connectedness, one chain cover, exclusion from the local exceptions, two independent eigenmodes at $\theta=8$, and the contradiction with the claimed upper bound. Parameterized shifted-matrix kernel identities and independence hold for every $R\ge1$; the native recurrence identification is formalized at $R=2$.

## Falsifier

A proof of the original universal claim would contradict `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.result`. The unresolved infinite native-graph extension and any amended universal bound are outside this result.

## Evidence

- Kernel-checked declaration: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.result : ¬ claim`.
- Frozen state: `Golden/Frozen/state/D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.lean.json`.
- The targeted Lean build and scoped report both exit 0; the axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.
- The exact checker is pinned at [`the-omega-institute/trureturing-experiments@daff737da5c5f9b6946de114e69753ecde01e652`](https://github.com/the-omega-institute/trureturing-experiments/tree/daff737da5c5f9b6946de114e69753ecde01e652/docs/reports/mandal-manna-dq-dilworth), path `docs/reports/mandal-manna-dq-dilworth/check.py`. Running `python3 .lake/scratch/mandal-manna-check.py` on the immutable file exits 0 with `ALL_CHECKS_OK`; its SHA-256 is `413df9e09713c58a2de0802c3dbe4c372a66cc4caa82c9b0a0c3430395225d9e`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Triage

- **Proved — collision mechanism.** Two independent global modes have eigenvalue $\theta=8$ in the eight-vertex graph, the vicinal cover has one chain, and $8$ is outside the local-exception set. Evidence: kernel-checked declarations `u8_mode`, `v8_mode`, `mode8_independent`, `dilworth8_eq`, `no_local8`, and `result`.
- **Proved — parameterized extent.** The matrix-kernel identities and independence hold for every $R\ge1$; the native recurrence counterexample is formalized at $R=2$ (the source parameter $r=1$). Evidence: kernel-checked declarations `familyU_kernel`, `familyV_kernel`, and `family_independent`, with the native instance consumed by `result`.
- **Computed — finite family check.** The pinned exact checker validates source-family members $r=1,\ldots,12$, with nullity exactly two in each tested member. Command: `python3 .lake/scratch/mandal-manna-check.py`; exit code 0; script SHA-256 `413df9e09713c58a2de0802c3dbe4c372a66cc4caa82c9b0a0c3430395225d9e`. Uniform extension beyond this tested range is open.
- **Open — infinite-family formalization.** A full Lean formalization of recurrence-defined native graphs for all $r\ge1$ and exact multiplicity two uniformly is not supplied.
- **Open — surviving neighbours.** The settlement refutes the DQ bound as stated. It does not settle adjacency multiplicity bounds away from $0$ and $-1$, distance-matrix bounds, or any amended DQ bound.

### What the settlement shows

The failure mechanism is a repeated nonlocal distance-signless eigenvalue in a graph whose vicinal width is one; the local-exception mechanism does not remove this eigenvalue. The parameterized matrix identities show the mode construction persists for all $R\ge1$, while the native graph bridge is certified at $R=2$. The exact checker supports the first twelve source-family members only. The source's distance-Laplacian statement, local-mode and quotient formulas, and Example 5.4 remain outside the refutation; no amended universal DQ bound is claimed.

## ASSUMED-UNVERIFIED

The literature screen is bounded. OpenAlex and Semantic Scholar citation queries returned HTTP 429, and the older DQ papers and the Crossref-returned survey were not fully read. The absence of a published settlement and any priority conclusion therefore remain `ASSUMED-UNVERIFIED`.
