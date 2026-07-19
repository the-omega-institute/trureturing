---
bibkey: zurek2003decoherence
title: Decoherence, einselection, and the quantum origins of the classical
doi: 10.1103/RevModPhys.75.715
claim: Environmental monitoring suppresses coherence between selected pointer states.
strata_touched:
  - D5/S3/Quantum/Decoherence
  - D5/S3/Quantum/QubitWitnesses
license: citation-only
triage: anchor
---

# Decoherence, einselection, and the quantum origins of the classical

Wojciech H. Zurek reviews environment-induced decoherence and pointer-state
selection. It anchors the standard phase-damping skeleton formalized here:
diagonal populations are preserved while off-diagonal coherence is attenuated.
The composition and fixed-point declarations in `D5/S3/Quantum/Decoherence`
record two algebraic consequences of that stipulated map.

The Lean module assumes a real phase-damping map and proves its finite iterate
algebraically. It does not derive that map from a Hamiltonian, identify the
repository ledger with a physical environment, equate bookkeeping with
decoherence, or make the address principle an einselection law.

## Search log

- 2026-07-17: Queried `"Decoherence, einselection, and the quantum origins of
  the classical" DOI 10.1103/RevModPhys.75.715` through NyxID/Tavily. APS
  returned Wojciech Hubert Zurek, the exact title, `Rev. Mod. Phys. 75, 715`,
  publication on 22 May 2003, and the DOI. arXiv `quant-ph/0105127` returned
  the same title and journal reference.
- 2026-07-17: Queried `Zurek decoherence off diagonal coherence pointer states
  diagonal populations phase damping`. Original-review excerpts state that
  pointer states remain untouched while their superpositions lose phase
  coherence. INSPIRE similarly states that environmental monitoring destroys
  coherence between pointer states.
- 2026-07-17: No search result was used to attribute the observer source's
  ledger-specific causal claims to Zurek. Those clauses remain unresolved.
- 2026-07-18: Crossref returned Wojciech H. Zurek, the exact review title,
  publication date 22 May 2003, and DOI `10.1103/RevModPhys.75.715`.
  The arXiv record `quant-ph/0105127v3` independently matched the title, author,
  journal reference, and DOI.
- 2026-07-18: Checked the arXiv PDF directly. The review states that
  einselected pointer states are stable, that monitored open-system states
  diagonalize in the pointer basis, and that off-diagonal terms are controlled
  by an environment-overlap decoherence factor. This supports the stipulated
  channel skeleton, not the observer atom's ledger/environment identification.
- 2026-07-18: The APS DOI target returned HTTP 403 to automated retrieval. No
  content conclusion was drawn from that failed route; the matching arXiv
  version supplied the successful original-text check.

## Verified locator

- DOI: https://doi.org/10.1103/RevModPhys.75.715
- APS: https://link.aps.org/doi/10.1103/RevModPhys.75.715
- arXiv: https://arxiv.org/abs/quant-ph/0105127
