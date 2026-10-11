# EmptyRowFillingConstruction

## Abstract

EmptyRowFillingConstruction for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Definition 1.1 (Counted).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , \operatorname{Counted} r k d : \operatorname{Type}\\\forall (r k d : \mathbb{N}) , \operatorname{Counted} r k d = (\left\{R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType} | \operatorname{IsASR} R \land \operatorname{ExtAvoids312} R \land \operatorname{nonemptyRows} R = d\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.Counted` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.2 (S_outside).**

$$\forall (r k d : \mathbb{N}) , (r < d \lor k < d) \to (S r k d : \mathbb{Z}) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.S_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.3 (nonemptyRows_eq_card_subtype).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{nonemptyRows} R = \operatorname{Nat} . \operatorname{card} \left\{i : \operatorname{Fin} r | \exists j : \operatorname{Fin} k , R i j \neq 0\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.nonemptyRows_eq_card_subtype` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.4 (first_empty_row_exists).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{nonemptyRows} R = k) \to (k < r) \to \exists (j : \operatorname{Fin} (k + 1)) (\operatorname{hj} : j . \operatorname{val} < r) , (\forall c , R \langle \operatorname{val} j , \operatorname{hj}\rangle c = 0) \land (\forall i : \operatorname{Fin} r , i . \operatorname{val} < j . \operatorname{val} \to \exists c , R i c \neq 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.first_empty_row_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.5 (topRows_nonemptyRows_of_before).**

$$\forall (r k p : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hp} : p \le r) , (\forall i : \operatorname{Fin} r , i . \operatorname{val} < p \to \exists c , R i c \neq 0) \to \operatorname{nonemptyRows} (\operatorname{topRows} R \operatorname{hp}) = p$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.topRows_nonemptyRows_of_before` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.6 (tailRows).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (i_{0} : \operatorname{Fin} r) , \operatorname{tailRows} (r := r) (k := k) R i_{0} : \operatorname{Finset} (\operatorname{Fin} r)\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (i_{0} : \operatorname{Fin} r) , \operatorname{tailRows} (r := r) (k := k) R i_{0} = (\operatorname{univ} . \operatorname{filter} (\operatorname{fun} i : \operatorname{Fin} r \mapsto i_{0} < i \land (\exists j : \operatorname{Fin} k , R i j \neq 0)))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.7 (tailColumn).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hR} : \operatorname{IsASR} R) , \forall (\operatorname{he} : \operatorname{ExtAvoids312} R) , \forall (\operatorname{hd} : \operatorname{nonemptyRows} R = k) , \forall (i_{0} : \operatorname{Fin} r) , \forall (\operatorname{hempty} : \forall j , R i_{0} j = 0) , \forall (i : \operatorname{tailRows} R i_{0}) , \operatorname{tailColumn} (r := r) (k := k) R \operatorname{hR} \operatorname{he} \operatorname{hd} i_{0} \operatorname{hempty} i : \operatorname{Fin} k\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hR} : \operatorname{IsASR} R) , \forall (\operatorname{he} : \operatorname{ExtAvoids312} R) , \forall (\operatorname{hd} : \operatorname{nonemptyRows} R = k) , \forall (i_{0} : \operatorname{Fin} r) , \forall (\operatorname{hempty} : \forall j , R i_{0} j = 0) , \forall (i : \operatorname{tailRows} R i_{0}) , \operatorname{tailColumn} (r := r) (k := k) R \operatorname{hR} \operatorname{he} \operatorname{hd} i_{0} \operatorname{hempty} i = (\operatorname{Classical} . \operatorname{choose} (\mathord{\cdot} : \exists a : \operatorname{Fin} k , \forall j : \operatorname{Fin} k , R i . \operatorname{val} j = \operatorname{if} a = j \operatorname{then} 1 \operatorname{else} 0))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailColumn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Classical.choose selects a column from the displayed existential singleton proposition. The placeholder suppresses its proof; the ASR, avoidance, row-count and empty-row hypotheses remain explicit.

**Lemma 1.8 (tailColumn_entries).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hR} : \operatorname{IsASR} R) , \forall (\operatorname{he} : \operatorname{ExtAvoids312} R) , \forall (\operatorname{hd} : \operatorname{nonemptyRows} R = k) , \forall (i_{0} : \operatorname{Fin} r) , \forall (\operatorname{hempty} : \forall j , R i_{0} j = 0) , \forall (i : \operatorname{tailRows} R i_{0}) , \forall (j : \operatorname{Fin} k) , R i . \operatorname{val} j = \operatorname{if} \operatorname{tailColumn} R \operatorname{hR} \operatorname{he} \operatorname{hd} i_{0} \operatorname{hempty} i = j \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailColumn_entries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.9 (balancedTailEquiv).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hR} : \operatorname{IsASR} R) , \forall (\operatorname{he} : \operatorname{ExtAvoids312} R) , \forall (\operatorname{hd} : \operatorname{nonemptyRows} R = k) , \forall (i_{0} : \operatorname{Fin} r) , \forall (\operatorname{hempty} : \forall j , R i_{0} j = 0) , \operatorname{balancedTailEquiv} (r := r) (k := k) R \operatorname{hR} \operatorname{he} \operatorname{hd} i_{0} \operatorname{hempty} : \operatorname{Equiv} (\operatorname{tailRows} R i_{0}) (\operatorname{deficientColumns} (\operatorname{topRows} (p := i_{0} . \operatorname{val}) R \mathord{\cdot}))\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hR} : \operatorname{IsASR} R) , \forall (\operatorname{he} : \operatorname{ExtAvoids312} R) , \forall (\operatorname{hd} : \operatorname{nonemptyRows} R = k) , \forall (i_{0} : \operatorname{Fin} r) , \forall (\operatorname{hempty} : \forall j , R i_{0} j = 0) , \forall (i : \operatorname{tailRows} R i_{0}) , (\operatorname{balancedTailEquiv} R \operatorname{hR} \operatorname{he} \operatorname{hd} i_{0} \operatorname{hempty}) . \operatorname{toFun} i = \langle \operatorname{tailColumn} R \operatorname{hR} \operatorname{he} \operatorname{hd} i_{0} \operatorname{hempty} i\rangle\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.balancedTailEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The forward map sends each nonempty row below the empty row to its unique 1-column, via Equiv.ofBijective. The inverse is the unique preimage; proof fields are suppressed.

**Lemma 1.10 (balancedTailEquiv_strictAnti).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hR} : \operatorname{IsASR} R) , \forall (\operatorname{he} : \operatorname{ExtAvoids312} R) , \forall (\operatorname{hd} : \operatorname{nonemptyRows} R = k) , \forall (i_{0} : \operatorname{Fin} r) , \forall (\operatorname{hempty} : \forall j , R i_{0} j = 0) , \operatorname{StrictAnti} (\operatorname{fun} i \mapsto (\operatorname{balancedTailEquiv} R \operatorname{hR} \operatorname{he} \operatorname{hd} i_{0} \operatorname{hempty} i) . \operatorname{val})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.balancedTailEquiv_strictAnti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.11 (strictAnti_equiv_sorted).**

$$\forall (\alpha \beta : \operatorname{Type}*) , [\operatorname{LinearOrder} \alpha] \to [\operatorname{LinearOrder} \beta] \to \forall (s : \operatorname{Finset} \alpha) , \forall (t : \operatorname{Finset} \beta) , \forall (e : \operatorname{Equiv} s t) , (\operatorname{StrictAnti} (\operatorname{fun} x : s \mapsto (e x) . \operatorname{val})) \to \forall (n : \mathbb{N}) , \forall (\operatorname{hs} : s . \operatorname{card} = n) , \forall (\operatorname{ht} : t . \operatorname{card} = n) , \forall (x : \operatorname{Fin} n) , e (s . \operatorname{orderIsoOfFin} \operatorname{hs} x) = t . \operatorname{orderIsoOfFin} \operatorname{ht} x . \operatorname{rev}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.strictAnti_equiv_sorted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.12 (tailIndex).**

$$\begin{aligned}\forall (r p : \mathbb{N}) , \forall (\operatorname{hp} : p < r) , \forall (a : \operatorname{Fin} (r - p - 1)) , \operatorname{tailIndex} (r := r) (p := p) \operatorname{hp} a : \operatorname{Fin} r\\\forall (r p : \mathbb{N}) , \forall (\operatorname{hp} : p < r) , \forall (a : \operatorname{Fin} (r - p - 1)) , \operatorname{tailIndex} (r := r) (p := p) \operatorname{hp} a = (\langle p + 1 + a . \operatorname{val}\rangle)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.13 (tailChoice).**

$$\begin{aligned}\forall (r k p : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hp} : p < r) , \operatorname{tailChoice} (r := r) (k := k) (p := p) R \operatorname{hp} : \operatorname{Finset} (\operatorname{Fin} (r - p - 1))\\\forall (r k p : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hp} : p < r) , \operatorname{tailChoice} (r := r) (k := k) (p := p) R \operatorname{hp} = (\operatorname{univ} . \operatorname{filter} (\operatorname{fun} a : \operatorname{Fin} (r - p - 1) \mapsto \exists c : \operatorname{Fin} k , R (\operatorname{tailIndex} \operatorname{hp} a) c \neq 0))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.14 (mem_tailChoice).**

$$\forall (r k p : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hp} : p < r) , \forall (a : \operatorname{Fin} (r - p - 1)) , a \in \operatorname{tailChoice} R \operatorname{hp} \Leftrightarrow \exists c , R (\operatorname{tailIndex} \operatorname{hp} a) c \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.mem_tailChoice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.15 (tailChoiceEquiv).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (i_{0} : \operatorname{Fin} r) , \operatorname{tailChoiceEquiv} (r := r) (k := k) R i_{0} : \operatorname{Equiv} (\operatorname{tailRows} R i_{0}) (\operatorname{tailChoice} R i_{0} . \operatorname{isLt})\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (i_{0} : \operatorname{Fin} r) , ((\operatorname{tailChoiceEquiv} R i_{0}) . \operatorname{toFun} = (\operatorname{fun} i \mapsto \langle \langle i . \operatorname{val} . \operatorname{val} - i_{0} . \operatorname{val} - 1\rangle\rangle)) \land ((\operatorname{tailChoiceEquiv} R i_{0}) . \operatorname{invFun} = (\operatorname{fun} a \mapsto \langle \operatorname{tailIndex} i_{0} . \operatorname{isLt} a . \operatorname{val}\rangle))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailChoiceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted. The two equalities give the toFun and invFun fields; subtype proof fields are suppressed.

**Lemma 1.16 (first_empty_choice_card).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to (\operatorname{nonemptyRows} R = k) \to \forall (i_{0} : \operatorname{Fin} r) , (\forall c , R i_{0} c = 0) \to (\forall i : \operatorname{Fin} r , i . \operatorname{val} < i_{0} . \operatorname{val} \to \exists c , R i c \neq 0) \to (\operatorname{tailChoice} R i_{0} . \operatorname{isLt}) . \operatorname{card} = k - i_{0} . \operatorname{val}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.first_empty_choice_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.17 (fillTail).**

$$\begin{aligned}\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \forall (i : \operatorname{Fin} t) , \forall (c : \operatorname{Fin} k) , \operatorname{fillTail} (j := j) (k := k) (t := t) T A \operatorname{hA} i c : \operatorname{SignType}\\\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \forall (i : \operatorname{Fin} t) , \forall (c : \operatorname{Fin} k) , \operatorname{fillTail} (j := j) (k := k) (t := t) T A \operatorname{hA} i c = (\operatorname{if} \exists x , (A . \operatorname{orderEmbOfFin} \operatorname{hA}) x = i \land \operatorname{deficientColumnAt} T x = c \operatorname{then} 1 \operatorname{else} 0)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.fillTail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.18 (fillTail_selected_row).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \forall (x : \operatorname{Fin} (\operatorname{deficientColumns} T) . \operatorname{card}) , \operatorname{fillTail} T A \operatorname{hA} ((A . \operatorname{orderEmbOfFin} \operatorname{hA}) x) = \operatorname{fun} c \mapsto \operatorname{if} \operatorname{deficientColumnAt} T x = c \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.fillTail_selected_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.19 (selectedRowAt_surjective).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \forall (i : \operatorname{Fin} t) , (i \in A) \to \exists x , (A . \operatorname{orderEmbOfFin} \operatorname{hA}) x = i$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.selectedRowAt_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.20 (fillTail_unselected_row).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \forall (i : \operatorname{Fin} t) , (i \neg \in A) \to \operatorname{fillTail} T A \operatorname{hA} i = \operatorname{fun} \mathord{\cdot} \mapsto 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.fillTail_unselected_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.21 (filledRect).**

$$\begin{aligned}\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \operatorname{filledRect} (j := j) (k := k) (t := t) T A \operatorname{hA} : \operatorname{Matrix} (\operatorname{Fin} (j + (1 + t))) (\operatorname{Fin} k) \operatorname{SignType}\\\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \operatorname{filledRect} (j := j) (k := k) (t := t) T A \operatorname{hA} = (\operatorname{Fin} . \operatorname{append} T (\operatorname{Fin} . \operatorname{append} (\operatorname{fun} \mathord{\cdot} \mapsto 0) (\operatorname{fillTail} T A \operatorname{hA})))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.22 (filledRect_top).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \forall (i : \operatorname{Fin} j) , \forall (c : \operatorname{Fin} k) , \operatorname{filledRect} T A \operatorname{hA} (i . \operatorname{castAdd} (1 + t)) c = T i c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.23 (filledRect_empty).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \forall (c : \operatorname{Fin} k) , \operatorname{filledRect} T A \operatorname{hA} (\operatorname{Fin} . \operatorname{natAdd} j (0 : \operatorname{Fin} (1 + t))) c = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.24 (filledRect_tail).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \forall (i : \operatorname{Fin} t) , \forall (c : \operatorname{Fin} k) , \operatorname{filledRect} T A \operatorname{hA} (\operatorname{Fin} . \operatorname{natAdd} j (\operatorname{Fin} . \operatorname{natAdd} 1 i)) c = \operatorname{fillTail} T A \operatorname{hA} i c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.25 (filledRect_isASR).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} T) \to \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \operatorname{IsASR} (\operatorname{filledRect} T A \operatorname{hA})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_isASR` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.26 (filledRect_nonemptyRows).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} T) \to \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \operatorname{nonemptyRows} (\operatorname{filledRect} T A \operatorname{hA}) = k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_nonemptyRows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.27 (rowComplete_nonempty).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{nonemptyRows} R = r) \to \forall (i : \operatorname{Fin} r) , \exists j , R i j \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.rowComplete_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.28 (filledRect_extAvoids312).**

$$\forall (j k t : \mathbb{N}) , \forall (T : \operatorname{Matrix} (\operatorname{Fin} j) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} T) \to (\operatorname{ExtAvoids312} T) \to (\operatorname{nonemptyRows} T = j) \to \forall (A : \operatorname{Finset} (\operatorname{Fin} t)) , \forall (\operatorname{hA} : A . \operatorname{card} = (\operatorname{deficientColumns} T) . \operatorname{card}) , \operatorname{ExtAvoids312} (\operatorname{filledRect} T A \operatorname{hA})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_extAvoids312` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.Counted`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.S_outside`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.balancedTailEquiv`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.balancedTailEquiv_strictAnti`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.fillTail`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.fillTail_selected_row`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.fillTail_unselected_row`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_empty`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_extAvoids312`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_isASR`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_nonemptyRows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_tail`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.filledRect_top`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.first_empty_choice_card`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.first_empty_row_exists`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.mem_tailChoice`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.nonemptyRows_eq_card_subtype`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.rowComplete_nonempty`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.selectedRowAt_surjective`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.strictAnti_equiv_sorted`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailChoice`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailChoiceEquiv`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailColumn`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailColumn_entries`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailIndex`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.tailRows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction.topRows_nonemptyRows_of_before`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion](CanonicalCompletion.md)
