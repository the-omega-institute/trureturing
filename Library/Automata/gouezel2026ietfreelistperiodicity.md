---
bibkey: gouezel2026ietfreelistperiodicity
authors: Sébastien Gouëzel
year: 2026
title: "IETFree/ListPeriodicity.lean (Lean source artifact, revision 48a23a630f39ae7c439b9efcbd03e729c18406fd)"
doi: null
url: https://github.com/sgouezel/IETFree/blob/48a23a630f39ae7c439b9efcbd03e729c18406fd/IETFree/ListPeriodicity.lean
claim: "For arbitrary alphabet types, equality of flattened natural powers with both exponents nonzero implies commutation of the words, including empty words."
strata_touched:
  - D5/S1/Words/Powers/CommonPositivePowers
license: Apache-2.0
triage: anchor
---

## Verified locator

Source: https://github.com/sgouezel/IETFree/blob/48a23a630f39ae7c439b9efcbd03e729c18406fd/IETFree/ListPeriodicity.lean

Sébastien Gouëzel, IETFree/ListPeriodicity.lean, immutable revision
`48a23a630f39ae7c439b9efcbd03e729c18406fd`. This reference identifies a
Lean source artifact and its version, without journal or DOI metadata.
The source at the immutable URL above has
9328 bytes, SHA-256
`f857ec2235717a1e5d2c034d339dad0b7e5ac1ca454bd6043154139c0066fa0b`.
Lines 47–168 contain the needed proof closure; lines 102–105 state
`List.append_comm_of_flatten_replicate_eq`.

## Exact statement and correspondence

For every universe u, every type A in Type u, all lists w and v over A,
and natural numbers M and N, if M is nonzero, N is nonzero, and
`(List.replicate M w).flatten = (List.replicate N v).flatten`, then
`w ++ v = v ++ w`. Empty words are allowed. No finiteness, ordering,
inhabitedness or decidable equality assumption on A is present. Both
nonzero assumptions are retained without claiming that each is
separately necessary or sharp.

D5/S1/Words/Powers/CommonPositivePowers.lean contains four private
period/reassembly helpers and the public theorem
`D5.S1.Words.Powers.CommonPositivePowers.append_comm_of_flatten_replicate_eq`.
The Fine–Wilf gcd-period and block-reassembly proof is transplanted;
ring normalization is expressed by elementary natural-number rewrites.
The private block lemmas include zero block length; the public positive-exponent assumptions remain unchanged.
No unrelated prefix-comparison lemma or group code is included.
CyclicCentralizer uses this theorem to establish compatibility of
positive-power roots of the same word. This theorem alone proves no
centralizer classification or unique-generator conclusion. The full
target's primary reference remains Library/Automata/lothaire1983words.md.
This is reused source content, without a discovery claim.

## License and retirement

Original copyright 2026 Sébastien Gouëzel; the original copyright and
author notice accompanies the transplanted Lean source. The complete
Apache 2.0 license is docs/reports/licenses/ietfree-LICENSE.txt. The
supplied complete upstream tree contains no NOTICE path.

Retire each transplanted declaration when this repository's own pinned
Mathlib supplies an equivalent same-signature List declaration,
especially `List.append_comm_of_flatten_replicate_eq`. Replace the
corresponding transplant by direct import and application of that
pinned declaration. Acceptance elsewhere without presence in this
repository's pin does not trigger retirement.
