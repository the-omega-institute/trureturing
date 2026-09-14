---
bibkey: erdos1985consecutive
authors: Paul Erdős
year: 1985
title: "Problems and results on consecutive integers and prime factors of binomial coefficients"
doi: 10.1216/RMJ-1985-15-2-353
claim: "Put (21) ∏_{i=1}^{k} (x + i) = u_k(x) v_k(x), (u_k(x), v_k(x)) = 1 where v_k(x) is squarefree and all prime factors of u_k(x) occur with an exponent greater than 1. The representation in (21) is clearly unique. Clearly for k > k_0(x), u_k(x) > v_k(x). Perhaps one can estimate the smallest k_0(x) so that u_k(x) > v_k(x) for all k > k_0(x) quite well. I have not done this. For small values of k usually v_k(x) > u_k(x). I thought that for every x there is a k for which v_k(x) > u_k(x). x = 7 seemed a likely counterexample but if k = 7, u_7(7) = 2^7 3^3 < v_7(7) = 5·7·11·13. On the other hand a simple computation shows that n = 23 is a counterexample, i.e., for every k, v_k(23) < u_k(23). The reason for this is the existence of 24, 25, 27 and 32. I would not be surprised if 23 is the only counterexample. Perhaps in fact there is a k_0 so that for every k > k_0 and all n > n_0(k) (22) v_k(n) > u_k(n). (22) is perhaps too optimistic."
strata_touched:
  - D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation
license: citation-only
triage: anchor
---

# Erdős's consecutive-product factorization question

The paper separates each consecutive product into the primes occurring once
and the prime powers whose exponents exceed one, then discusses how the two
factors compare.

## Verified locator

- DOI: 10.1216/RMJ-1985-15-2-353
- URL: https://users.renyi.hu/~p_erdos/1985-27.pdf
- Locator: page 361 of the Rocky Mountain Journal of Mathematics article.
- COMMENT (verbatim): Put (21) ∏_{i=1}^{k} (x + i) = u_k(x) v_k(x), (u_k(x), v_k(x)) = 1 where v_k(x) is squarefree and all prime factors of u_k(x) occur with an exponent greater than 1. The representation in (21) is clearly unique. Clearly for k > k_0(x), u_k(x) > v_k(x). Perhaps one can estimate the smallest k_0(x) so that u_k(x) > v_k(x) for all k > k_0(x) quite well. I have not done this. For small values of k usually v_k(x) > u_k(x). I thought that for every x there is a k for which v_k(x) > u_k(x). x = 7 seemed a likely counterexample but if k = 7, u_7(7) = 2^7 3^3 < v_7(7) = 5·7·11·13. On the other hand a simple computation shows that n = 23 is a counterexample, i.e., for every k, v_k(23) < u_k(23). The reason for this is the existence of 24, 25, 27 and 32. I would not be surprised if 23 is the only counterexample. Perhaps in fact there is a k_0 so that for every k > k_0 and all n > n_0(k) (22) v_k(n) > u_k(n). (22) is perhaps too optimistic.

Only the sentence "I would not be surprised if 23 is the only counterexample"
is refuted: the starting value 47 has `u_k(47) > v_k(47)` for every positive
`k`; conjecture (22) and the statement about the starting value 23 are untouched.
