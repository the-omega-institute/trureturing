# RecurrenceSeries

## Abstract

RecurrenceSeries for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Definition 1.1 (T).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , T r k d : \mathbb{Z}\\\forall (r k d : \mathbb{N}) , T r k d = (\operatorname{if} r < d \lor k < d \operatorname{then} 0 \operatorname{else} \operatorname{if} d = 0 \operatorname{then} 1 \operatorname{else} \operatorname{if} r = d \land k = d \operatorname{then} (\operatorname{Nat} . \operatorname{largeSchroder} (d - 1) : \mathbb{Z}) \operatorname{else} \operatorname{if} d = r \operatorname{then} T r (k - 1) d + T (r - 1) (k - 1) (d - 1) + \sum_{i : \operatorname{CoeSort}.\operatorname{coe} (\operatorname{Icc} 2 d)} (\operatorname{Nat} . \operatorname{largeSchroder} (i . \operatorname{val} - 2) : \mathbb{Z}) \cdot T (r + 1 - i . \operatorname{val}) (k + 1 - i . \operatorname{val}) (d + 1 - i . \operatorname{val}) \operatorname{else} \operatorname{if} d = k \operatorname{then} \sum_{j : \operatorname{Fin} (k + 1)} T j . \operatorname{val} k j . \operatorname{val} \cdot (\operatorname{Nat} . \operatorname{choose} (r - j . \operatorname{val} - 1) (k - j . \operatorname{val}) : \mathbb{Z}) \operatorname{else} T r (k - 1) d + T (r - 1) (k - 1) (d - 1) + \sum_{i : \operatorname{CoeSort}.\operatorname{coe} (\operatorname{Icc} 2 d)} (\operatorname{Nat} . \operatorname{largeSchroder} (i . \operatorname{val} - 2) : \mathbb{Z}) \cdot (T (r + 1 - i . \operatorname{val}) (k + 1 - i . \operatorname{val}) (d + 1 - i . \operatorname{val}) - (\operatorname{Nat} . \operatorname{choose} (r - i . \operatorname{val}) (d + 1 - i . \operatorname{val}) : \mathbb{Z})))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.2 (RecurrenceSpec).**

$$\begin{aligned}\forall (f : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{Z}) , \operatorname{RecurrenceSpec} f : \operatorname{Prop}\\\forall (f : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{Z}) , \operatorname{RecurrenceSpec} f \Leftrightarrow ((\forall r k d , r < d \lor k < d \to f r k d = 0) \land (\forall r k , f r k 0 = 1) \land (\forall d , 0 < d \to f d d d = (\operatorname{Nat} . \operatorname{largeSchroder} (d - 1) : \mathbb{Z})) \land (\forall r k , 0 < r \to r < k \to f r k r = f r (k - 1) r + f (r - 1) (k - 1) (r - 1) + \sum_{i : \operatorname{CoeSort}.\operatorname{coe} (\operatorname{Icc} 2 r)} (\operatorname{Nat} . \operatorname{largeSchroder} (i . \operatorname{val} - 2) : \mathbb{Z}) \cdot f (r + 1 - i . \operatorname{val}) (k + 1 - i . \operatorname{val}) (r + 1 - i . \operatorname{val})) \land (\forall r k , 0 < k \to k < r \to f r k k = \sum_{j : \operatorname{Fin} (k + 1)} f j . \operatorname{val} k j . \operatorname{val} \cdot (\operatorname{Nat} . \operatorname{choose} (r - j . \operatorname{val} - 1) (k - j . \operatorname{val}) : \mathbb{Z})) \land (\forall r k d , 0 < d \to d < r \to d < k \to f r k d = f r (k - 1) d + f (r - 1) (k - 1) (d - 1) + \sum_{i : \operatorname{CoeSort}.\operatorname{coe} (\operatorname{Icc} 2 d)} (\operatorname{Nat} . \operatorname{largeSchroder} (i . \operatorname{val} - 2) : \mathbb{Z}) \cdot (f (r + 1 - i . \operatorname{val}) (k + 1 - i . \operatorname{val}) (d + 1 - i . \operatorname{val}) - (\operatorname{Nat} . \operatorname{choose} (r - i . \operatorname{val}) (d + 1 - i . \operatorname{val}) : \mathbb{Z}))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.RecurrenceSpec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Theorem 1.3 (recurrence_unique).**

$$\forall (f : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{Z}) , (\operatorname{RecurrenceSpec} f) \to \forall r k d , f r k d = T r k d$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.recurrence_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.4 (q).**

$$\begin{aligned}q : (\operatorname{PowerSeries} \mathbb{Q})\\q = (X \cdot R)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.5 (A).**

$$\begin{aligned}A : (\operatorname{PowerSeries} \mathbb{Q})\\A = (1 + q)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.6 (U).**

$$\begin{aligned}U : (\operatorname{PowerSeries} \mathbb{Q})\\U = ((1 - q) ^{-1})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.7 (V).**

$$\begin{aligned}V : (\operatorname{PowerSeries} \mathbb{Q})\\V = ((1 - X) ^{-1})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.V` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.8 (G).**

$$\begin{aligned}\forall (a b : \mathbb{N}) , G a b : (\operatorname{PowerSeries} \mathbb{Q})\\\forall (a b : \mathbb{N}) , G a b = (C (1 / 2 : \mathbb{Q}) \cdot A \cdot (R ^{b} \cdot U ^{a} + V ^{a}))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.G` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.9 (q_constant).**

$$\operatorname{constantCoeff} q = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.q_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.10 (U_left).**

$$U \cdot (1 - q) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.U_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.11 (V_left).**

$$V \cdot (1 - (X : (\operatorname{PowerSeries} \mathbb{Q}))) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.V_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.12 (R_as_q).**

$$R = (1 + q) \cdot U$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.R_as_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.13 (half_cancel).**

$$(2 : (\operatorname{PowerSeries} \mathbb{Q})) \cdot C (1 / 2 : \mathbb{Q}) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.half_cancel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.14 (transform).**

$$\begin{aligned}\forall (B Q : (\operatorname{PowerSeries} \mathbb{Q})) , \operatorname{transform} B Q : (\operatorname{PowerSeries} \mathbb{Q})\\\forall (B Q : (\operatorname{PowerSeries} \mathbb{Q})) , \operatorname{transform} B Q = (\operatorname{mk} \operatorname{fun} n \mapsto \operatorname{coeff} n (B \cdot Q ^{n}))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.transform` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.15 (transform_eq).**

$$\forall (B Q \operatorname{Qinv} u : (\operatorname{PowerSeries} \mathbb{Q})) , (\operatorname{constantCoeff} u = 0) \to (u = X \cdot Q . \operatorname{subst} u) \to (\operatorname{Qinv} \cdot Q = 1) \to \operatorname{transform} B Q = (B \cdot \operatorname{Qinv}) . \operatorname{subst} u \cdot \operatorname{derivative} \mathbb{Q} u$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.transform_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.16 (z).**

$$\begin{aligned}z : (\operatorname{PowerSeries} \mathbb{Q})\\z = (X \cdot V ^{2})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.17 (z_constant).**

$$\operatorname{constantCoeff} z = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.z_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.18 (even_Catalan_identity).**

$$1 + z \cdot (\operatorname{P}13\operatorname{CatalanLagrangeBridge}.\operatorname{catalanUnit} . \operatorname{subst} z + \operatorname{P}13\operatorname{CatalanLagrangeBridge}.\operatorname{catalanUnit} . \operatorname{subst} (- z)) = A \cdot V$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.even_Catalan_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.19 (finite_mul_subst).**

$$\forall (A B u : (\operatorname{PowerSeries} \mathbb{Q})) , (\operatorname{constantCoeff} u = 0) \to \forall (n : \mathbb{N}) , \operatorname{coeff} n (A \cdot B . \operatorname{subst} u) = \sum_{p \in \operatorname{range} (n + 1)} \operatorname{coeff} p B \cdot \operatorname{coeff} n (A \cdot u ^{p})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.finite_mul_subst` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.20 (mul_pow_vanish).**

$$\forall (A u : (\operatorname{PowerSeries} \mathbb{Q})) , (\operatorname{constantCoeff} u = 0) \to \forall (n p : \mathbb{N}) , (n < p) \to \operatorname{coeff} n (A \cdot u ^{p}) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.mul_pow_vanish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.21 (even_sum_reindex).**

$$\forall (n : \mathbb{N}) , \forall (f : \mathbb{N} \to \mathbb{Q}) , (\sum_{p \in \operatorname{range} (n + 1)} \operatorname{if} \operatorname{Even} p \operatorname{then} f p \operatorname{else} 0) = \sum_{i \in \operatorname{range} (n + 1)} \operatorname{if} 2 \cdot i \le n \operatorname{then} f (2 \cdot i) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.even_sum_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.22 (Cnt).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , \operatorname{Cnt} r k d : \mathbb{Q}\\\forall (r k d : \mathbb{N}) , \operatorname{Cnt} r k d = (\operatorname{if} r < d \lor k < d \operatorname{then} 0 \operatorname{else} \operatorname{coeff} d (G (r - d) (k - d)))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.Cnt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.23 (Cnt_admissible).**

$$\forall (r k d : \mathbb{N}) , (d \le r) \to (d \le k) \to \operatorname{Cnt} r k d = \operatorname{coeff} d (G (r - d) (k - d))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.Cnt_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.24 (series_eq_T).**

$$\forall (r k d : \mathbb{N}) , \operatorname{Cnt} r k d = (T r k d : \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.series_eq_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.A`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.Cnt`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.Cnt_admissible`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.G`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.R_as_q`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.RecurrenceSpec`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.T`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.U`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.U_left`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.V`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.V_left`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.even_Catalan_identity`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.even_sum_reindex`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.finite_mul_subst`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.half_cancel`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.mul_pow_vanish`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.q`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.q_constant`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.recurrence_unique`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.series_eq_T`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.transform`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.transform_eq`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.z`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.z_constant`
- Dependency: [D5/S1/Recurrence/Algebraic/SchroderIntegralEGF](../../../S1/Recurrence/Algebraic/SchroderIntegralEGF.md)
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity](../../../S1/Recurrence/Invariants/CatalanCubicCompositionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/TripleIterateProductModFour](../../../S1/Recurrence/Invariants/TripleIterateProductModFour.md)
- Dependency: [D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve](../../../S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge](../Nonnesting/CatalanLagrangeBridge.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo](../Nonnesting/NonnestingOneThreeTwoTwo.md)
