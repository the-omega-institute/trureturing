# The row product of A320043

## Abstract

The terms of row n of A320043 multiply to B(n+1)³, where B(N)=∏ k/gcd(k,N); B(p)=(p−1)! at primes.

**Theorem 1.1 (Row product, diagonal term and prime values).**

Lean statement: `D5/S3/ArithSums/SpeziaA320043RowProduct.result`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/SpeziaA320043RowProduct.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *OEIS A320043, COMMENTS, revision 43: a square-value refutation extending Zhu's Pell-prime result (2011)*. DOI: [10.5281/zenodo.24058057](https://doi.org/10.5281/zenodo.24058057). URL: <https://zenodo.org/records/24058057>.

*Commentary.*

Let X(n,k)=(n+1−k)²k/gcd(n+1−k,k)³, the n-th antidiagonal of S. Spezia's triangle A322550 (whose row sums are A320043), and B(N)=∏_{k=1}^{N} k/gcd(k,N), which is OEIS A119619 (Fuller). Then X(2m−1,m)=1 for m ≥ 1; for n ≥ 1, ∏_{k=1}^{n} X(n,k)=B(n+1)³, equivalently the positive real cube roots of the terms multiply to B(n+1); and B(p)=(p−1)! for every prime p. Put N=n+1 and g=gcd(k,N). Since gcd(N−k,k)=gcd(N−k,N)=g, each term splits exactly as X(n,k)=((N−k)/gcd(N−k,N))²·(k/g). The reflection k ↦ N−k is a bijection of {1,…,n}, so the first factors multiply to the same value P=∏_{k=1}^{n} k/gcd(k,N) as the second ones, giving P³; and B(N)=P because the term k=N equals 1. For a prime p, gcd(k,p)=1 when k<p, so B(p)=(p−1)!. The product identity is Spezia's 2024 formula on A322550, proved as Corollary 6 of H. Ma and W. Zhang's note on A320043 (DOI 10.5281/zenodo.24058057); the prime value B(p)=(p−1)! is Steinerberger's comment on A119619.

## References

- Truth anchor: `D5/S3/ArithSums/SpeziaA320043RowProduct.result`
