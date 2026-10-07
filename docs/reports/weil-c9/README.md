# Conditional actual c9 retained comparison

This package publishes project-authored scientific programs and previously computed matrices for one sufficient Weil comparison at the actual support half-width $a=\log3$. It reuses the source formulas and support-independent Gamma moment input described in the [Library note](../../../Library/Weil/liu2026tailcompensation.md). It does not reproduce an author's old finite certificate, claim originality for those formulas, or prove RH.

The kernel input is conditional on the author's assertion that the pinned moment intervals contain their exact scalar moments. Neither the input hashes nor this replay prove that assertion. The numerical source contract has a separate paper/code review. A separate native Codex CLI session completed a full replay of the same program on the same hash-bound matrix inputs and independently inspected the new result. This supplies independent execution, with the producer's arithmetic environment reused after direct version checks; independent implementation, matrix regeneration and moment containment remain unverified.

## Replay

Use CPython **3.13.12**, `python-flint==0.9.0` and `numpy==2.5.3`. These are checked version strings, not binary attestation of the interpreter, extension or linked arithmetic libraries. From the repository root, with `python` selecting that interpreter:

```sh
python -m venv build/weil-c9-venv
build/weil-c9-venv/bin/python -m pip install -r docs/reports/weil-c9/requirements.txt
build/weil-c9-venv/bin/python docs/reports/weil-c9/reproduce.py --out-dir build/weil-c9-reproduction
```

The wrapper verifies all listed scientific program hashes and both packed and decoded matrix hashes. It decodes the published snapshots into the chosen output directory, then runs the directed consumer. The consumer reads each input and manifest once and hashes the same bytes it parses. A successful sign run exits zero and writes `result.json`, including the full exact dyadic trial and all directed pivot enclosures. Any other exit is unsuccessful; validation exceptions need not return the consumer's final exit code 2.

For bindings alone, append `--check-inputs-only`. That mode performs no sign calculation. Full replay at the pinned 1536-bit precision took 14.90 seconds in the producer's local environment; this is an observed runtime, not a bound for another machine.

[`result-summary.json`](result-summary.json) preserves the producer's local replay and adds a compact `independent_execution` record against the same exact manifest. The separate session ran the full wrapper at 1536 bits with exit zero, checked all 256 serialized pivot lower endpoints as strictly positive, and recomputed the exact squared Frobenius norm from all 65,536 trial integers, verifying the bound 32. The floating negative proposal has a positive directed quadratic enclosure, so it supplies no directed negative witness. The record binds the fresh full result by its hash without publishing another trial or pivot snapshot. A replay writes those entries into its full result. Elapsed times and floating proposals are not byte-reproducibility requirements. The scientific success requirement is **all 256 directed pivots strictly positive and no directed negative witness**.

## Objects and comparison

All three centers belong to the same actual even Legendre embedding

$$
E_j(u)=\sqrt{\frac{4j+1}{2a}}P_{2j}(u/a),\qquad j=0,\ldots,255,
\qquad a=\log3.
$$

The prime input supplies $A_0$ approximating $E^*M_9E$ and $B_0$ approximating **$E^*M_9^2E$**. The clipped prime-power shifts are $2,3,4,5,7,8$; the endpoint shift 9 has zero overlap. The second matrix is not $A_0^2$. The kernel center $J_0$ includes the newly normalized polynomial kernel and the actual polynomial-filtered even rank-one tail update.

Every matrix center is an exact symmetric rational matrix on the $2^{-512}$ grid. The reused prime and kernel arithmetic operator allowances are at most $2^{-504}$. The kernel's analytic replacement is paid under the moment-containment premise. The consumer uses $\epsilon_J=2^{-205}$ to pay both that replacement and the directed finite assembly error.

For the exact rational trial $X$ on the $2^{-256}$ grid, its integer sum of squares verifies $\|X\|\le\|X\|_F\le32$. With $\mu=4/5$, the source inverse-residual supplier and the matrix-error allowances give

$$
W=X+X^*-X^*A_0X+
\mu^{-1}(I-A_0X-X^*A_0+X^*B_0X)+\Delta_XI,
$$

$$
\Delta_X=1104\epsilon_A+1280\epsilon_B,
\qquad W\succeq G=E^*M_9^{-1}E\succ0.
$$

Thus $W^{-1}\preceq G^{-1}$, the direction required for a sufficient lower comparison. With $D_0=B_0-A_0^2$ and

$$
\epsilon_D=\epsilon_B+(2(2011/325)+\epsilon_A)\epsilon_A,
$$

the matrix tested by the consumer is

$$
T=W^{-1}+J_0-\epsilon_JI-2^{-187}I
-2^{-186}(D_0+\epsilon_DI).
$$

The common-embedding projection and complementary-block allowances $e=2^{-188}$, $n=2^{-390}$ and $h=2^{-386}$, and the coefficient comparisons underlying this sufficient target, are in the Library note's **A common 256-mode consumer** section. They are paper-level source applications, not additional kernel-verified declarations supplied by this package.

The consumer's NumPy calculation only proposes a possible negative vector. Its sign is checked by directed arithmetic against $T$. Complete directed LDL checks the positive sign. The recorded minimum pivot lower bound is about $1.91066\times10^{-6}$; it is **not a minimum eigenvalue bound**. Neither this finite comparison nor positivity on a single bounded support supplies the cofinal support family required for RH.

## Input provenance and optional regeneration

`input-manifest.json` binds the original reused matrix bytes, the public programs and their selected environment. The `.b64` files contain base64-encoded zlib streams of the exact original JSON files; compression changes neither matrix centers nor decoded hashes. The matrix producer programs are provided for inspection and optional regeneration. Their hashes identify bytes, not an independently witnessed execution history.

The prime input was computed with `c9_prime_ball_matrices.py --size 256 --bits 4096`; its original run took 1795.43 seconds. Replay deliberately reuses this input. Rebuild only when inspecting or independently checking its production:

```sh
build/weil-c9-venv/bin/python docs/reports/weil-c9/c9_prime_ball_matrices.py --size 256 --bits 4096 --out build/weil-c9-reproduction/regenerated-prime.json
```

The kernel producer uses `--size 256 --bits 3072` and the external `--moments` packet. Its pinned source is [Liu's certified-weil-positivity repository](https://github.com/luciferyu666/certified-weil-positivity/tree/b6cd2183c1e79c6c27a34267812a7b2d73ed1b59), release `v1.0-mcom-submission`, member `w200-pub-2026-09-14/reproduction/release-run/certificates/moments.json`, SHA-256 `f8cb5c681a22755b980d2e98d781353fe9ce058fe33eb8a7753585e2c52b2f93`. It has 1024 rows on the packet-wide 1024-bit grid, band 256 and background $7/2$.

Obtain that external input subject to its publisher's rights and verify its digest before optional regeneration. The author's packet, implementation, manuscript and old certificates are not included here. The kernel producer's output metadata records the containment premise; running it does not independently validate the moment oracle.

```sh
build/weil-c9-venv/bin/python docs/reports/weil-c9/c9_kernel_ball_matrices.py --moments /path/to/moments.json --size 256 --bits 3072 --out build/weil-c9-reproduction/regenerated-kernel.json
```

Regeneration changes runtime metadata, so complete output-file hashes can differ even when the scientific centers agree. To consume genuinely changed scientific inputs, bind their bytes and errors in a new manifest and execute the target again; an old result cannot be relabeled as certifying a new manifest.
