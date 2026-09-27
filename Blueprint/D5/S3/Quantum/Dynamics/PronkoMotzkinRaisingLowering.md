# Raising and lowering operators of the periodic Motzkin chain

## Abstract

On the periodic Motzkin spin-1 chain with N at least 2 sites, the operators Sigma^+ and Sigma^-, the sums of the products of local powers s_i^{r_i} with r_1 + ... + r_N equal to 1, respectively -1, commute with the periodic Hamiltonian, send each ground state v_m to a nonzero multiple of v_(m+1), respectively v_(m-1), and annihilate v_N, respectively v_(-N). This proves Conjecture 2 of Pronko.

**Definition 1.1 (Heights of the letters).**

$$\operatorname{ht}\left(0\right) = 1 \land \left(\operatorname{ht}\left(1\right) = 0 \land \operatorname{ht}\left(2\right) = -1\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.ht` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

The letters u, f, d (basis vectors 0, 1, 2 of C^3) have heights 1, 0 and -1: the steps of a Motzkin path.

**Definition 1.2 (The spin-1 raising matrix).**

$$sp = \operatorname{matrix}\left((0,1,0), (0,0,1), (0,0,0)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.sp` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

The basis vectors 0, 1, 2 of C^3 are u, f and d (up, flat, down); s^+ is the 0/1 matrix of eq. spin1rep.

**Definition 1.3 (The spin-1 lowering matrix).**

$$sm = \operatorname{matrix}\left((0,0,0), (1,0,0), (0,1,0)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.sm` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

s^- is the 0/1 matrix of eq. spin1rep.

**Definition 1.4 (Local powers).**

$$(\operatorname{spow}\left(0\right) = sm^{2}) \land \left((\operatorname{spow}\left(1\right) = sm) \land \left((\operatorname{spow}\left(2\right) = 1) \land \left((\operatorname{spow}\left(3\right) = sp) \land (\operatorname{spow}\left(4\right) = sp^{2})\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.spow` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

s^r for r = -2, ..., 2, indexed by k = r + 2: s^0 is the identity, s^{±1} = s^±, s^{±2} = (s^±)^2.

**Definition 1.5 (Exponents).**

$$\operatorname{rv}\left(r\right) = r - 2$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.rv` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

The index r = 0, ..., 4 of the local powers stands for the exponent r - 2 = -2, ..., 2.

**Definition 1.6 (An operator on one site).**

$$\operatorname{site}\left(i, A\right)\left(a, b\right) = \operatorname{if} \forall k \in \operatorname{Fin}\left(N\right),\; \operatorname{ne}\left(k, i\right) \Rightarrow (\operatorname{a}\left(k\right) = \operatorname{b}\left(k\right)) \operatorname{then} A\left(\operatorname{a}\left(i\right), \operatorname{b}\left(i\right)\right) \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.site` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

site(i, A) acts as the 3 x 3 matrix A on the i-th tensor factor and as the identity on the others (eq. spmsz).

**Definition 1.7 (The operators Sigma^+ and Sigma^-).**

$$\operatorname{Sig}\left(N, e\right) = \sum_{r \in \{r \in \operatorname{Fin}\left(5\right)^{N} \mid \sum_{i \in \operatorname{Fin}\left(N\right)} \operatorname{rv}\left(\operatorname{r}\left(i\right)\right) = e\}} \operatorname{prod}\left(\operatorname{ofFn}\left((i \mapsto \operatorname{site}\left(i, \operatorname{spow}\left(\operatorname{r}\left(i\right)\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.Sig` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

Sig(N, 1) is Sigma^+ and Sig(N, -1) is Sigma^- of eq. Sigmapmsum: the sum, over the exponent vectors r in {-2, ..., 2}^N with r_1 + ... + r_N = e, of the ordered product s_1^{r_1} ... s_N^{r_N}.

**Definition 1.8 (The height S^z of a word).**

$$\operatorname{S}\left(a\right) = \sum_{i \in \operatorname{Fin}\left(N\right)} \operatorname{ht}\left(\operatorname{a}\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.S` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

The eigenvalue of the third component of the total spin on a basis word: the number of u minus the number of d, with ht(u) = 1, ht(f) = 0, ht(d) = -1.

**Definition 1.9 (Two-site basis vectors).**

$$\operatorname{ket}\left(x, y\right) = \operatorname{single}\left((x,y), 1\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.ket` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

ket(x, y) is the basis vector |x y> of C^3 (x) C^3: the function on pairs that is 1 at (x, y) and 0 elsewhere.

**Definition 1.10 (Half projectors).**

$$\operatorname{proj}\left(w\right) = \frac{1}{2} \cdot \operatorname{vecMulVec}\left(w, w\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.proj` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

proj(w) = (1/2) w w^T, one half of the product of w with its transpose (Matrix.vecMulVec, no complex conjugation); for the three real vectors in piProj this is (1/2)|w><w|.

**Definition 1.11 (The local projector Pi).**

$$piProj = \operatorname{proj}\left(\operatorname{ket}\left(0, 1\right) - \operatorname{ket}\left(1, 0\right)\right) + \operatorname{proj}\left(\operatorname{ket}\left(2, 1\right) - \operatorname{ket}\left(1, 2\right)\right) + \operatorname{proj}\left(\operatorname{ket}\left(0, 2\right) - \operatorname{ket}\left(1, 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.piProj` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

piProj is Pi = U + D + F of eq. UDF, with U = (1/2)(|uf> - |fu>)(<uf| - <fu|), D = (1/2)(|df> - |fd>)(<df| - <fd|) and F = (1/2)(|ud> - |ff>)(<ud| - <ff|), where u, f, d are the basis vectors 0, 1, 2.

**Definition 1.12 (An operator on two sites).**

$$\operatorname{twoSite}\left(i, j, P\right)\left(a, b\right) = \operatorname{if} \forall k \in \operatorname{Fin}\left(N\right),\; \left(\operatorname{ne}\left(k, i\right) \land \operatorname{ne}\left(k, j\right)\right) \Rightarrow (\operatorname{a}\left(k\right) = \operatorname{b}\left(k\right)) \operatorname{then} P\left((\operatorname{a}\left(i\right),\operatorname{a}\left(j\right)), (\operatorname{b}\left(i\right),\operatorname{b}\left(j\right))\right) \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.twoSite` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

twoSite(i, j, P) acts as the 9 x 9 matrix P with its first factor on site i and its second on site j, and as the identity on the other sites.

**Definition 1.13 (The periodic Hamiltonian).**

$$\operatorname{H}\left(N\right) = \sum_{i \in \operatorname{Fin}\left(N\right)} \operatorname{twoSite}\left(i, \operatorname{finRotate}\left(N, i\right), piProj\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.H` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

H^periodic of eq. Hpbc: Pi on the sites i, i + 1 for i = 1, ..., N - 1 and Pi_{N,1} on the sites N, 1; with the sites numbered 0, ..., N - 1 these are the pairs i, finRotate(N, i) with finRotate the cyclic shift i -> i + 1 mod N.

**Definition 1.14 (The ground states v_m).**

$$\operatorname{v}\left(N, m\right)\left(a\right) = \operatorname{if} \operatorname{S}\left(a\right) = m \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.v` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

v_m is the sum of the paths from (0, 0) to (N, m) with steps in {-1, 0, 1} (Conjecture 1): the sum of the basis words of height m.

**Definition 1.15 (Conjecture 2).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; 2 \le N \Rightarrow (\left(\operatorname{Sig}\left(N, 1\right) \cdot \operatorname{H}\left(N\right) = \operatorname{H}\left(N\right) \cdot \operatorname{Sig}\left(N, 1\right) \land \operatorname{Sig}\left(N, -1\right) \cdot \operatorname{H}\left(N\right) = \operatorname{H}\left(N\right) \cdot \operatorname{Sig}\left(N, -1\right)\right) \land \left(\left(\forall m \in \mathbb{Z},\; \left(-N \le m \land m < N\right) \Rightarrow (\exists c \in \mathbb{C},\; \operatorname{ne}\left(c, 0\right) \land \operatorname{mulVec}\left(\operatorname{Sig}\left(N, 1\right), \operatorname{v}\left(N, m\right)\right) = c \cdot \operatorname{v}\left(N, m + 1\right))\right) \land \left(\left(\forall m \in \mathbb{Z},\; \left(-N < m \land m \le N\right) \Rightarrow (\exists c \in \mathbb{C},\; \operatorname{ne}\left(c, 0\right) \land \operatorname{mulVec}\left(\operatorname{Sig}\left(N, -1\right), \operatorname{v}\left(N, m\right)\right) = c \cdot \operatorname{v}\left(N, m - 1\right))\right) \land \left(\operatorname{mulVec}\left(\operatorname{Sig}\left(N, 1\right), \operatorname{v}\left(N, N\right)\right) = 0 \land \operatorname{mulVec}\left(\operatorname{Sig}\left(N, -1\right), \operatorname{v}\left(N, -N\right)\right) = 0\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.claim` (`✓ std3`).

*Citation.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

For N at least 2: Sigma^+ and Sigma^- commute with H; for -N <= m < N, Sigma^+ v_m is a nonzero multiple of v_(m+1); for -N < m <= N, Sigma^- v_m is a nonzero multiple of v_(m-1); and Sigma^+ v_N = 0, Sigma^- v_(-N) = 0 (eqs. Sigmavec and SpmH).

**Theorem 1.16 (Proof of Conjecture 2).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.result` (`✓ std3`). ∎

*Resolves.* `Problems/pronko-2025-motzkin-raising-lowering` (proved) by `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pronko-2025-motzkin-raising-lowering","declaration_gid":"D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. G. Pronko (2025). *Periodic Motzkin chain: Ground states and symmetries*. DOI: [10.48550/arXiv.2504.00835](https://doi.org/10.48550/arXiv.2504.00835). URL: <https://arxiv.org/abs/2504.00835v3>.

*Commentary.*

An ordered product of operators on distinct sites has as entry at a, b the product of the local entries. The entry of s^r at x, y is 1 when ht(x) = ht(y) + r and 0 otherwise, so for given basis words a and b exactly one exponent vector, r_i = ht(a_i) - ht(b_i), gives a nonzero product, and Sig(N, e) has entry 1 at a, b when S(a) = S(b) + e and 0 otherwise; that is, Sigma^± is the sum over m of |v_(m±1)><v_m|. Each of U, D, F pairs two basis states of the same height sum with opposite signs, so every row of Pi sums to zero over each height class; hence every two-site term, and H, annihilate every v_m, and H is symmetric, so v_m^T H = 0 as well. Therefore H Sigma^± = 0 = Sigma^± H. Finally Sigma^± v_m = T_m v_(m±1), where T_m, the number of words of height m, is positive for |m| <= N, while no word has height ±(N + 1).

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.H`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.S`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.Sig`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.ht`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.ket`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.piProj`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.proj`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.rv`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.site`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.sm`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.sp`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.spow`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.twoSite`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.v`
