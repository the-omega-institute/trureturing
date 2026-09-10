# Search receipts

HTTP success is distinguished from a usable search result. Google returned only a JavaScript redirect shell; these queries are invalid negative evidence.

| Request | HTTP | Bytes | SHA-256 | Interpretation |
|---|---:|---:|---|---|
| https://oeis.org/A375178/internal | 200 | 11833 | 7801e7b99911c475ca46326d0face00c43cac95a49ca2946636df838c2ae6d1b | retrieved; content assessment below |
| https://oeis.org/A375178/b375178.txt | 200 | 369 | f173ce2dc1b5e2183e105c557b5f1005fcf5b333ffe1dc6b21fd0b099e558f5d | retrieved; content assessment below |
| https://api.github.com/search/code?q=A375178+language%3ALean | 401 | 120 | b7dbd173f33b19650f61b1c528737e2037cf768d90076fdfce5d32541765e29e | invalid request; no negative evidence |
| https://arxiv.org/pdf/1111.3057 | 200 | 338199 | d2a9fb84c854c4937d38aedda75c1ed6fc5fbb234abbfdba76ec40facef2979d | retrieved; content assessment below |
| https://api.github.com/search/repositories?q=wolstenholme+lean | 200 | 55 | 4af480b8ee5b87b369a76c49bd22c9a783908272ebffbe97898f8ab0f0772a5f | retrieved; content assessment below |
| https://leansearch.net/ | 200 | 6573 | 2c555c512dad5d28196d5b3a6098163e15ff61349d28da1e2979f2bbca10b266 | homepage reached; not a query result |
| https://reservoir.lean-lang.org/ | 200 | 115518 | cc504927f480af574c3fad96053941a720162b6b4b23ff5452e3def7eae9777b | homepage reached; not a query result |
| https://raw.githubusercontent.com/project-numina/LeanTriathlon/2aede4209c203ae9901eff870744e4b77dc6173f/LiveLeanTriathlonSorry/Wolstenholme/All.lean | 200 | 491 | aa11bd8fb68bda5afecec08f65455ccbcafd2437cf3003069a376ca0cd6c6931 | retrieved; content assessment below |
| https://www.google.com/search?q=%22binomial%22+%22p%5E5%22+%22Sun%22 | 200 | 91326 | 987b9e2410876a937b9a6d46231afbd4974daa2a9638bde47749ce2a08c9b052 | invalid search: redirect shell, no results |
| https://www.google.com/search?q=%22A375178%22 | 200 | 91359 | ae36a1c16fff812aac60c1db96acfb7ce0a96ae9702e52d77dbb24711d3f478e | invalid search: redirect shell, no results |
| https://export.arxiv.org/api/query?search_query=all%3AA375178 | 200 | 696 | 70518df2cb7a841aa95c8c32b480eb5379567d08b20ec3fd125e76bdcf8c770f | retrieved; content assessment below |
| https://www.google.com/search?q=%22supercongruence%22+%22binomial%22+%22p%2Bk%22 | 200 | 91302 | d6db4656053343734a71facc51a5c6bcd68c7af1eac375a936b935e7f740a9e3 | invalid search: redirect shell, no results |
| authenticated gh api: A375178 language:Lean | 200 | 415 | 4eec3ebfe58bf0a1857a1fba2cd313435a0a7b819c0426d9c8b9d76cf10c0a8e | response includes HTTP headers |
| authenticated gh api: wolstenholme language:Lean | 200 | 10618 | 6082672b6adf4b84c825ef23875d2e3d93525a956f98fce577cb4e76674cc97c | response includes HTTP headers |

## Assessments

- OEIS internal page still explicitly says “We conjecture” for the p⁵ statement. Its only bibliographical link is the Meštrović survey. Its b-file has exactly 19 terms, all equal to the independently computed values.
- arXiv exact sequence query: totalResults=0, valid response. No claim beyond this indexed query.
- GitHub authenticated code search A375178 language:Lean: total_count=0, incomplete_results=false.
- GitHub authenticated code search wolstenholme language:Lean: two hits in project-numina/LeanTriathlon; one is an import, the other an unproved statement ending in sorry. The latter file was read completely at immutable revision 2aede4209c203ae9901eff870744e4b77dc6173f. It provides no usable proof or supporting public lemmas.
- GitHub repository search wolstenholme lean: total_count=0. This repository query does not supersede the two code-search hits.
- Pinned mathlib v4.33.0: no A375178 or Wolstenholme declaration found. The broad harmonic/congruence regex has one irrelevant Euler–Mascheroni prose hit. FiniteField.sum_pow_units and FiniteField.sum_pow_lt_card_sub_one were found and their public statements and proofs inspected; they supply finite-field power sums and must be reused.
- Meštrović PDF retrieved (31 pages). Detailed harmonic and binomial-sum assessment is pending; PDF extraction initially warned about missing fontTools, so the affected mathematical typography is not yet reliable.

## Cache

make lean-cache-ensure exited 0: status=seeded, method=clonefile, clonefile_attempts=1, stamp_miss=null, mathlib_olean_state=warm, project_olean_state=warm, mathlib_missing_olean_files=0. Donor: /Users/chronoai/trureturing.
