---
bibkey: bosma2025using
authors: Wieb Bosma, Rene Bruin, Robbert Fokkink, Jonathan Grube, Anniek Reuijl, Thian Tromp
year: 2025
title: Using Walnut to solve problems from the OEIS
doi: 10.48550/arXiv.2503.04122
claim: Conjecture 17 gives a two-parameter periodic characterization of the greedy three-sumfree sequence with seeds 1, g, g+d.
strata_touched:
  - D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter
license: citation-only
triage: anchor
---

# Using Walnut to solve problems from the OEIS

This note anchors only printed Conjecture 17 in *Journal of Integer Sequences*
28 (2025), Article 25.3.8, page 18, for
`Problems/greedy-three-sumfree-two-parameter.md`. Conjecture 6 in
arXiv:2503.04122v1 is the earlier form of the same conjecture and is **not the
same statement**: it bounds the periodic branch by `z > g+d`, which is false at
the third seed, and the printed version corrects that to `z >= g+d`. The anchor
is the printed version, which is what the Lean statement matches. The paper calls it a meta-conjecture based on
"firm computational evidence, from an implementation in Magma".

The caller-supplied reading, 2026-09-07, transcribes the printed statement as:

> Let d >= 2. For every g >= d + 1 the greedy 3-sumfree sequence S_{1,g,g+d}
> is characterized as follows: z in S_{1,g,g+d} <=> z in {1, g, 2g+d-1, 2g+d}
> or z >= g+d and z mod 5g+2d in {g+d-2, g+d-1, ..., 2g+d-2}.

On printed page 16, `S_{x,y,z}` is the increasing positive integer sequence
with seeds `x < y < z`. Each later entry is the least integer larger than its
predecessor that is not the sum of three different previous entries, indexed
`i < j < k`. Distinctness is part of the definition.

The frozen module `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter` defines
`S` through `greedyPrefix`, seeded by the reversed list `[g+d, g, 1]`, with
`Nat.find` selecting the least next admissible integer. Its `RestrictedThreeSum`
requires `x < y < w`; its public `conjecture17` has the displayed membership
criterion under `2 <= d` and `d+1 <= g`. The caller compared both the statement
and the greedy definition with the printed source. This is a human reading,
not a machine-checked equivalence between the source and Lean.

The repository theory volume's candidate 6.225 records a 2026-09-06 check that
Shtrezi, arXiv:2606.17447, addresses only Conjecture 16, with seeds `1,g,g+1`.
That is repository context, not a fresh literature search for this note.

## Search log

- Caller-supplied reading, 2026-09-07: queried
  `https://export.arxiv.org/api/query?id_list=2503.04122`, HTTP 200,
  `totalResults=1`. The entry is arXiv:2503.04122v1 with the title and authors
  above, published `2025-03-06T06:00:43Z`, primary category `math.NT`.
  No `arxiv:doi` or `arxiv:journal_ref` was reported. API response byte count
  was not supplied.
- Caller-supplied reading, 2026-09-07:
  `HEAD https://doi.org/10.48550/arXiv.2503.04122` returned HTTP 302 to
  `https://arxiv.org/abs/2503.04122`; no response byte count was supplied.
- Caller-supplied reading, 2026-09-07: the printed PDF at
  `https://cs.uwaterloo.ca/journals/JIS/VOL28/Fokkink/fokkink9.pdf` returned
  HTTP 200, 1096283 bytes, 21 pages, SHA-256
  `ce0592a3d0e063a183e9cb590e5de328dfce782e3f84221a31120c0a56cfb8f5`.
  The caller extracted Conjecture 17 on page 18 and the greedy definition on
  page 16. Searching the extracted text for `10\.\d{4,9}/\S+` returned zero
  matches; the caller reports that JIS assigns no DOI to this article. The
  arXiv-assigned DOI is therefore the bound identity.
- Worker reading, 2026-09-07: read the local Lean definitions, public theorem,
  and frozen-state receipt. The HTTP resources above were not fetched again.

No literature search for a later resolution of the conjecture was performed; the
open status recorded in the problem candidate is the status stated in this
arXiv version, not an assessment of the subsequent literature.

## Verified locator

- arXiv: https://arxiv.org/abs/2503.04122v1 (Conjecture 6; caller-supplied).
- DOI: https://doi.org/10.48550/arXiv.2503.04122 (caller-supplied HTTP 302).
- Printed PDF: https://cs.uwaterloo.ca/journals/JIS/VOL28/Fokkink/fokkink9.pdf
  (Conjecture 17, page 18; definition, page 16; caller-supplied HTTP 200).
