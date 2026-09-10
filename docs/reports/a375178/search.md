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
- Meštrović PDF retrieved (31 pages). The initial extraction warned about missing fontTools; fontTools was installed in the attempt scratch environment and extraction repeated. Relevant source assessment follows below.

## Cache

make lean-cache-ensure exited 0: status=seeded, method=clonefile, clonefile_attempts=1, stamp_miss=null, mathlib_olean_state=warm, project_olean_state=warm, mathlib_missing_olean_files=0. Donor: /Users/chronoai/trureturing.

## Further source checks

- https://www.bing.com/search?format=rss&q=%22binomial%22%20%22supercongruence%22%20%22cubes%22: HTTP 200, 4495 bytes, SHA-256 86d375a0eeb5673dfa1d16748e1fcb699addbf024798666d9c671f84ffe287db.
- https://www.bing.com/search?format=rss&q=%22A112028%22%20congruence: HTTP 200, 5145 bytes, SHA-256 445c4d25a19c521f56f2d33461ddd55b82d4ddc9632e57c962f66cfb641097bc.
- https://export.arxiv.org/api/query?search_query=all%3A%22binomial%20sums%22%20AND%20all%3Acongruences&max_results=40: HTTP 200, 17941 bytes, SHA-256 291f1eed96e291feddf1cb36dd6fbc12a10f989375a9a919209647656f609727.
- https://arxiv.org/pdf/math/0301252: HTTP 200, 359195 bytes, SHA-256 9c34a4ac406c6bf0717149003fabede8e44887febdaee5c5af79b776a337f988.
- https://oeis.org/A112028/internal: HTTP 200, 13636 bytes, SHA-256 8cf0d42458dff907b40cb2760c254c224366e5b1cab0e6674193616059a6e467.
- https://core.ac.uk/download/pdf/301642554.pdf: HTTP 404, 0 bytes, SHA-256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.

The Bing RSS responses contain unrelated pizza/Yahoo results, so both are invalid
search evidence despite HTTP 200. The arXiv binomial-sums/congruences query returned
14 entries; titles and abstracts were read, none states the present sum's p⁵
congruence. This is a bounded abstract search, not a full-text exclusion.

OEIS A112028 is the same sequence with offset shifted: its comments attribute
the p⁵ conjecture to Peter Bala (2023) and specifically say Coster's Theorem 4
proves only p³. The CORE link to Coster returns 404 and is not negative evidence.
The conjecture's origin therefore predates the 2024 asymptotic comment on A375178.

Meštrović §§4 and 10 were read. Equations (21), (25) cover the odd harmonic
sum at exponent three; equations (60)–(66) concern different binomial sums
(with top entries p or p−1, or reciprocal binomials). They do not directly state
the target. Bayat's generalization has a qualification corrected by Zhao;
we do not use the unqualified survey paraphrase as a proof.

Zhao, “Wolstenholme type theorem for multiple harmonic sums”, arXiv:math/0301252:
Lemma 2.2 and its proof cover H(3;p−1)=0 mod p² for p≥7.
Theorem 3.2 covers H(1,3;p−1)=0 mod p for p≥7, indeed a stronger mod p²
formula. Equation (22) is the product/shuffle identity and Lemma 3.3 is
reversal. These are established prerequisites; they are not Lean dependencies.
The source's statements and relevant proofs were opened, not inferred from title.

## Final search batch and access limits

- https://doi.org/10.1007/BFb0091139: HTTP 200, 251635 bytes, SHA-256 5b3ea65640b0b37af04a1ca3f56473a9bb9c2faefc56e22dd81ccd0e41e406f4.
- https://api.crossref.org/works/10.1007/BFb0091139: HTTP 200, 8266 bytes, SHA-256 b775386c61524ace734033ebf761492616f80019b21930c12c8b32477a96ddf3.
- https://export.arxiv.org/api/query?search_query=all%3AA112028: HTTP 200, 696 bytes, SHA-256 6678aa2e26e385343f0db9561285fae35f4762274ccf28a4451e2fbe38c2cc3f.
- https://link.springer.com/content/pdf/10.1007/BFb0091139: HTTP 200, 251635 bytes, SHA-256 42f701daa1b9a75a0393af8ee25cce8c9d0d4626ecfa9a260f4b226ae6b8953c.

The A112028 arXiv query is valid and returns totalResults=0. Coster DOI and
Crossref metadata identify the 1990 chapter, pages 194–204. The publisher page
provides abstract and references with subscription access. The PDF route
returned HTML, not full text. Coster Theorem 4 has NOT been directly read; the
p³ attribution is secondhand from OEIS. Neither access failure is negative
evidence about the theorem.

- Local response artifact a375178-gh-harmonic.json: 477648 bytes, SHA-256 d780f50a5e46fe285f75c891aba7215532671c965979f8ec28e81139f2040f95.
- Local response artifact a375178-Usa2019P5.lean: 10877 bytes, SHA-256 dd1887118f0e06f565c2b82e1153552f6530bddc62c5ba7245e5ba6d5f8f90a1.

Authenticated GitHub code search harmonic ZMod language:Lean returned 92 hits
within the requested 100 results. Search metadata was examined; most hits were
mathlib copies/import collections. The candidate
https://github.com/dwrensha/compfiles/blob/master/Compfiles/Usa2019P5.lean
was read completely, including its public helper interfaces: it concerns
arithmetic/harmonic means and coprimality, not finite harmonic sum congruences.
Not all 92 file bodies were read; those bodies are ASSUMED-UNVERIFIED.
No usable Lean proof of the target or needed harmonic congruences was found
in the stated scope. Published prerequisites are locally proved under the
authorized fourth step of the repository search order.
