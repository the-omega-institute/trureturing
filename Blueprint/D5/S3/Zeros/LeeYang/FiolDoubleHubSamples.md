# Double-hub samples

## Abstract

The physical double-hub family: samples.

The two interlaced grids have a central defect. For d mod 4 equal to 0 or 1, insert pi/2. For residue 3 insert the positive central-gap point. For residue 2 replace the central zero by the two nearby points of opposite signs.

The resulting sequence has endpoints 0 and pi and contains exactly N+1 strictly increasing points. Its signs alternate strictly, so there are exactly N disjoint sign-changing intervals. The construction includes every residue and the cases d=2,3,4.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Definition 1.1 (baseSample).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines baseSample for the physical double-hub family.

**Theorem 1.2 (baseSample succ).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem baseSample_succ (d k : ℕ) (hd : 2 ≤ d) (hk : k+1 < N d) :     baseSample d k < baseSample d (k+1).

**Theorem 1.3 (baseSample signed).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_signed`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combines large-d estimates and exact small numerical premises for the complete sample domain. Exact source statement: theorem baseSample_signed (d k : ℕ) (hd : 2 ≤ d) (hk : k < N d)     (hnotzero : ¬(d%4=2 ∧ k=N d/2)) :     if k < N d/2 then 0 < (-1:ℝ)^k*(phaseValue d (baseSample d k)).re     else (-1:ℝ)^k*(phaseValue d (baseSample d k)).re < 0.

**Definition 1.4 (insertSample).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines insertSample for the physical double-hub family.

**Theorem 1.5 (insertSample succ).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves ordered insertion through all transition indices. Exact source statement: theorem insertSample_succ (b : ℕ → ℝ) (n mid : ℕ) (c : ℝ)     (hm : 0 < mid ∧ mid < n) (hb : ∀ k, k+1 < n → b k < b (k+1))     (hc : b (mid-1) < c ∧ c < b mid) (k : ℕ) (hk : k < n) :     insertSample b mid c k < insertSample b mid c (k+1).

**Definition 1.6 (replaceSample).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines replaceSample for the physical double-hub family.

**Theorem 1.7 (replaceSample succ).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves ordered replacement through all transition indices. Exact source statement: theorem replaceSample_succ (b : ℕ → ℝ) (n mid : ℕ) (l r : ℝ)     (hm : 0 < mid ∧ mid+1 < n) (hb : ∀ k, k+1 < n → b k < b (k+1))     (hc : b (mid-1)<l ∧ l<r ∧ r<b (mid+1)) (k : ℕ) (hk : k < n) :     replaceSample b mid l r k < replaceSample b mid l r (k+1).

**Theorem 1.8 (signed succ product).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.signed_succ_product`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.signed_succ_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem signed_succ_product (f : ℝ → ℝ) (s : ℕ → ℝ) (k : ℕ)     (ha : 0 < (-1:ℝ)^k*f (s k)) (hb : 0 < (-1:ℝ)^(k+1)*f (s (k+1))) :     f (s k)*f (s (k+1)) < 0.

**Theorem 1.9 (insertSample signed).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample_signed`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Preserves strict signed alternation through the inserted point. Exact source statement: theorem insertSample_signed (f : ℝ → ℝ) (b : ℕ → ℝ) (n mid : ℕ) (c : ℝ)     (hm : 0 < mid ∧ mid < n)     (hb : ∀ k, k<n → if k<mid then 0<(-1:ℝ)^k*f (b k) else (-1:ℝ)^k*f (b k)<0)     (hc : 0<(-1:ℝ)^mid*f c) (k : ℕ) (hk : k≤n) :     0<(-1:ℝ)^k*f (insertSample b mid c k).

**Theorem 1.10 (replaceSample signed).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample_signed`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Preserves strict signed alternation through both replacements. Exact source statement: theorem replaceSample_signed (f : ℝ → ℝ) (b : ℕ → ℝ) (n mid : ℕ) (l r : ℝ)     (hm : 0<mid ∧ mid+1<n) (he : Even mid)     (hb : ∀ k, k<n → k≠mid → if k<mid then 0<(-1:ℝ)^k*f (b k) else (-1:ℝ)^k*f (b k)<0)     (hl : 0<f l) (hr : f r<0) (k : ℕ) (hk : k≤n) :     0<(-1:ℝ)^k*f (replaceSample b mid l r k).

**Theorem 1.11 (baseSample last).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_last`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem baseSample_last (d : ℕ) (hd : 2≤d) : baseSample d (N d-1)=Real.pi.

**Theorem 1.12 (central insert data).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.central_insert_data`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.central_insert_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs the required central insertion for every applicable residue. Exact source statement: theorem central_insert_data (d : ℕ) (hd : 2≤d) (hi : d%4≠2) :     ∃ c : ℝ, baseSample d (N d/2-1)<c ∧ c<baseSample d (N d/2) ∧       0<(-1:ℝ)^(N d/2)*(phaseValue d c).re.

**Theorem 1.13 (central replace data).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.central_replace_data`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.central_replace_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs both required replacement points in residue2. Exact source statement: theorem central_replace_data (d : ℕ) (hd : 2≤d) (hi : d%4=2) :     Even (N d/2) ∧ ∃ l r : ℝ,       baseSample d (N d/2-1)<l ∧ l<r ∧ r<baseSample d (N d/2+1) ∧       0<(phaseValue d l).re ∧ (phaseValue d r).re<0.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_last`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_signed`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_succ`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.central_insert_data`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.central_replace_data`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample_signed`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.insertSample_succ`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample_signed`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.replaceSample_succ`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.signed_succ_product`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry](FiolDoubleHubRootGeometry.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
