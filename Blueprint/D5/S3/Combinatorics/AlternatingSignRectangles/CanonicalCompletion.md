# CanonicalCompletion

## Abstract

CanonicalCompletion for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Lemma 1.1 (last_minus_of_zero_sum).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to ((\sum_{i} (a i : \mathbb{Z})) = 0) \to \forall (x : \operatorname{Fin} n) , (a x \neq 0) \to (\forall y , x < y \to a y = 0) \to a x = - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.last_minus_of_zero_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.2 (pad_zero_line).**

$$\forall (n t : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to (\operatorname{EndsOne} a) \to \operatorname{Alternates} (\operatorname{Fin} . \operatorname{append} a (\operatorname{fun} \mathord{\cdot} : \operatorname{Fin} t \mapsto 0)) \land \operatorname{StartsOne} (\operatorname{Fin} . \operatorname{append} a (\operatorname{fun} \mathord{\cdot} : \operatorname{Fin} t \mapsto 0)) \land \operatorname{EndsOne} (\operatorname{Fin} . \operatorname{append} a (\operatorname{fun} \mathord{\cdot} : \operatorname{Fin} t \mapsto 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.pad_zero_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.3 (sum_pad_zero).**

$$\forall (n t : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\sum_{i} ((\operatorname{Fin} . \operatorname{append} a (\operatorname{fun} \mathord{\cdot} : \operatorname{Fin} t \mapsto 0) i : \operatorname{SignType}) : \mathbb{Z})) = \sum_{i} (a i : \mathbb{Z})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.sum_pad_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.4 (append_one_line).**

$$\forall (n t : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \forall (p : \operatorname{Fin} t) , (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to ((\sum_{i} (a i : \mathbb{Z})) = 0) \to \operatorname{Alternates} (\operatorname{Fin} . \operatorname{append} a (\operatorname{fun} j \mapsto \operatorname{if} p = j \operatorname{then} 1 \operatorname{else} 0)) \land \operatorname{StartsOne} (\operatorname{Fin} . \operatorname{append} a (\operatorname{fun} j \mapsto \operatorname{if} p = j \operatorname{then} 1 \operatorname{else} 0)) \land \operatorname{EndsOne} (\operatorname{Fin} . \operatorname{append} a (\operatorname{fun} j \mapsto \operatorname{if} p = j \operatorname{then} 1 \operatorname{else} 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.append_one_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.5 (sum_append_one).**

$$\forall (n t : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \forall (p : \operatorname{Fin} t) , (\sum_{i} ((\operatorname{Fin} . \operatorname{append} a (\operatorname{fun} j \mapsto \operatorname{if} p = j \operatorname{then} 1 \operatorname{else} 0) i : \operatorname{SignType}) : \mathbb{Z})) = (\sum_{i} (a i : \mathbb{Z})) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.sum_append_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.6 (RectContains312).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{RectContains312} (r := r) (k := k) R : \operatorname{Prop}\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{RectContains312} (r := r) (k := k) R \Leftrightarrow (\exists (i_{1} i_{2} i_{3} : \operatorname{Fin} r) (j_{1} j_{2} j_{3} : \operatorname{Fin} k) , i_{1} < i_{2} \land i_{2} < i_{3} \land j_{1} < j_{2} \land j_{2} < j_{3} \land R i_{1} j_{3} = 1 \land R i_{2} j_{1} = 1 \land R i_{3} j_{2} = 1)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.RectContains312` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.7 (extAvoids312_corner).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{ExtAvoids312} R) \to \neg \operatorname{RectContains312} R$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.extAvoids312_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.8 (no312_with_deficient_last).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{ExtAvoids312} R) \to \forall (i_{1} i_{2} : \operatorname{Fin} r) , \forall (j_{1} j_{2} j_{3} : \operatorname{Fin} k) , (i_{1} < i_{2}) \to (j_{1} < j_{2}) \to (j_{2} < j_{3}) \to (R i_{1} j_{3} = 1) \to (R i_{2} j_{1} = 1) \to (\operatorname{colSum} R j_{2} = 0) \to \operatorname{False}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.no312_with_deficient_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.9 (no12_with_empty_deficient).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{ExtAvoids312} R) \to \forall (i_{0} i_{1} : \operatorname{Fin} r) , \forall (j_{1} j_{2} : \operatorname{Fin} k) , (i_{0} < i_{1}) \to (j_{1} < j_{2}) \to (\forall j , R i_{0} j = 0) \to (R i_{1} j_{1} = 1) \to (\operatorname{colSum} R j_{2} = 0) \to \operatorname{False}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.no12_with_empty_deficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.10 (deficientColumnAt).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (x : \operatorname{Fin} (\operatorname{deficientColumns} R) . \operatorname{card}) , \operatorname{deficientColumnAt} (r := r) (k := k) R x : \operatorname{Fin} k\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (x : \operatorname{Fin} (\operatorname{deficientColumns} R) . \operatorname{card}) , \operatorname{deficientColumnAt} (r := r) (k := k) R x = ((\operatorname{deficientColumns} R) . \operatorname{orderEmbOfFin} \operatorname{rfl} x . \operatorname{rev})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.11 (deficientColumnAt_deficient).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (x : \operatorname{Fin} (\operatorname{deficientColumns} R) . \operatorname{card}) , \operatorname{colSum} R (\operatorname{deficientColumnAt} R x) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt_deficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.12 (deficientColumnAt_injective).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{Function} . \operatorname{Injective} (\operatorname{deficientColumnAt} R)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.13 (deficientColumnAt_antitone).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (x y : \operatorname{Fin} (\operatorname{deficientColumns} R) . \operatorname{card}) , (x < y) \to \operatorname{deficientColumnAt} R y < \operatorname{deficientColumnAt} R x$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.14 (deficientColumnAt_surjective).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (j : \operatorname{Fin} k) , (\operatorname{colSum} R j = 0) \to \exists x , \operatorname{deficientColumnAt} R x = j$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.15 (CompletionSafe).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{CompletionSafe} (r := r) (k := k) R : \operatorname{Prop}\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{CompletionSafe} (r := r) (k := k) R \Leftrightarrow ((\neg \operatorname{RectContains312} R) \land (\forall (i_{1} i_{2} : \operatorname{Fin} r) (j_{1} j_{2} j_{3} : \operatorname{Fin} k) , i_{1} < i_{2} \to j_{1} < j_{2} \to j_{2} < j_{3} \to R i_{1} j_{3} = 1 \to R i_{2} j_{1} = 1 \to \operatorname{colSum} R j_{2} = 0 \to \operatorname{False}) \land (\forall (i_{0} i_{1} i_{2} : \operatorname{Fin} r) (j_{1} j_{2} : \operatorname{Fin} k) , i_{0} < i_{1} \to i_{1} < i_{2} \to j_{1} < j_{2} \to (\forall j , R i_{0} j = 0) \to \neg (R i_{1} j_{1} = 1 \land R i_{2} j_{2} = 1)) \land (\forall (i_{0} i_{1} : \operatorname{Fin} r) (j_{1} j_{2} : \operatorname{Fin} k) , i_{0} < i_{1} \to j_{1} < j_{2} \to (\forall j , R i_{0} j = 0) \to R i_{1} j_{1} = 1 \to \operatorname{colSum} R j_{2} = 0 \to \operatorname{False}))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.CompletionSafe` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.16 (extAvoids312_iff_safe).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \operatorname{ExtAvoids312} R \Leftrightarrow \operatorname{CompletionSafe} R$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.extAvoids312_iff_safe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The four finite obstruction conditions are equivalent to the existence of an avoiding square completion.

**Definition 1.17 (StartsMinus).**

$$\begin{aligned}\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{StartsMinus} (n := n) a : \operatorname{Prop}\\\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{StartsMinus} (n := n) a \Leftrightarrow (\forall x , a x \neq 0 \to (\forall y , y < x \to a y = 0) \to a x = - 1)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.StartsMinus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.18 (concat_complete_opposite).**

$$\forall (n t : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \forall (b : \operatorname{Fin} t \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to (\operatorname{EndsOne} a) \to ((\sum_{i} (a i : \mathbb{Z})) = 1) \to (\operatorname{Alternates} b) \to (\operatorname{StartsMinus} b) \to \operatorname{Alternates} (\operatorname{Fin} . \operatorname{append} a b) \land \operatorname{StartsOne} (\operatorname{Fin} . \operatorname{append} a b)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.concat_complete_opposite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.19 (minus_singleton_line).**

$$\forall (n : \mathbb{N}) , \forall (p : \operatorname{Fin} n) , \operatorname{Alternates} (\operatorname{fun} x \mapsto \operatorname{if} x = p \operatorname{then} (- 1 : \operatorname{SignType}) \operatorname{else} 0) \land \operatorname{StartsMinus} (\operatorname{fun} x \mapsto \operatorname{if} x = p \operatorname{then} (- 1 : \operatorname{SignType}) \operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.minus_singleton_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.20 (minus_plus_line).**

$$\forall (n : \mathbb{N}) , \forall (x y : \operatorname{Fin} n) , (x < y) \to \operatorname{let} a := \operatorname{fun} z \mapsto \operatorname{if} z = x \operatorname{then} (- 1 : \operatorname{SignType}) \operatorname{else} \operatorname{if} z = y \operatorname{then} 1 \operatorname{else} 0 ; \operatorname{Alternates} a \land \operatorname{StartsMinus} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.minus_plus_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.CompletionSafe`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.RectContains312`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.StartsMinus`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.append_one_line`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.concat_complete_opposite`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt_antitone`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt_deficient`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt_injective`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.deficientColumnAt_surjective`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.extAvoids312_corner`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.extAvoids312_iff_safe`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.last_minus_of_zero_sum`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.minus_plus_line`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.minus_singleton_line`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.no12_with_empty_deficient`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.no312_with_deficient_last`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.pad_zero_line`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.sum_append_one`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion.sum_pad_zero`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/SignLines](SignLines.md)
