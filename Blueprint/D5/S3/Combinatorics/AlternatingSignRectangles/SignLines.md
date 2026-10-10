# SignLines

## Abstract

SignLines for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Lemma 1.1 (line_embed).**

$$\forall (n m : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \forall (b : \operatorname{Fin} m \to \operatorname{SignType}) , \forall (f : \operatorname{Fin} n \to \operatorname{Fin} m) , (\operatorname{StrictMono} f) \to (\forall u , b (f u) = a u) \to (\forall x , (\neg \exists u , f u = x) \to b x = 0) \to (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to \operatorname{Alternates} b \land \operatorname{StartsOne} b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.line_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.2 (ends_embed).**

$$\forall (n m : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \forall (b : \operatorname{Fin} m \to \operatorname{SignType}) , \forall (f : \operatorname{Fin} n \to \operatorname{Fin} m) , (\operatorname{StrictMono} f) \to (\forall u , b (f u) = a u) \to (\forall x , (\neg \exists u , f u = x) \to b x = 0) \to (\operatorname{EndsOne} a) \to \operatorname{EndsOne} b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.ends_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.3 (sum_embed).**

$$\forall (n m : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \forall (b : \operatorname{Fin} m \to \operatorname{SignType}) , \forall (f : \operatorname{Fin} n \to \operatorname{Fin} m) , (\operatorname{StrictMono} f) \to (\forall u , b (f u) = a u) \to (\forall x , (\neg \exists u , f u = x) \to b x = 0) \to (\sum_{u} (a u : \mathbb{Z})) = \sum_{x} (b x : \mathbb{Z})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.sum_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.4 (Alternates).**

$$\begin{aligned}\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{Alternates} (n := n) a : \operatorname{Prop}\\\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{Alternates} (n := n) a \Leftrightarrow (\forall x y , x < y \to a x \neq 0 \to a y \neq 0 \to (\forall z , x < z \to z < y \to a z = 0) \to a x \neq a y)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.Alternates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.5 (StartsOne).**

$$\begin{aligned}\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{StartsOne} (n := n) a : \operatorname{Prop}\\\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{StartsOne} (n := n) a \Leftrightarrow (\forall x , a x \neq 0 \to (\forall y , y < x \to a y = 0) \to a x = 1)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.StartsOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.6 (EndsOne).**

$$\begin{aligned}\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{EndsOne} (n := n) a : \operatorname{Prop}\\\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{EndsOne} (n := n) a \Leftrightarrow (\forall x , a x \neq 0 \to (\forall y , x < y \to a y = 0) \to a x = 1)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.EndsOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.7 (IsASR).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{IsASR} (r := r) (k := k) R : \operatorname{Prop}\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{IsASR} (r := r) (k := k) R \Leftrightarrow ((\forall i : \operatorname{Fin} r , \operatorname{Alternates} (R i) \land \operatorname{StartsOne} (R i) \land \operatorname{EndsOne} (R i)) \land (\forall j : \operatorname{Fin} k , \operatorname{Alternates} (\operatorname{fun} i : \operatorname{Fin} r \mapsto R i j) \land \operatorname{StartsOne} (\operatorname{fun} i \mapsto R i j)))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.IsASR` (`✓ std3`).

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Section 2 (p. 3): “Let r and k be positive integers. An alternating sign rectangle (ASR) of size r × k is an r × k matrix with entries in {−1, 0, 1} such that” “the nonzero entries alternate in each row and column;” “if a row contains a nonzero entry, then its leftmost and rightmost nonzero entries are 1;” “if a column contains a nonzero entry, then its topmost nonzero entry is 1.” Fin indices start at zero; the binding Lean conventions also include zero dimensions.

**Definition 1.8 (IsASM).**

$$\begin{aligned}\forall (m : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , \operatorname{IsASM} (m := m) M : \operatorname{Prop}\\\forall (m : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , \operatorname{IsASM} (m := m) M \Leftrightarrow (\operatorname{IsASR} M \land (\forall i , \sum_{j} (M i j : \mathbb{Z}) = 1) \land (\forall j , \sum_{i} (M i j : \mathbb{Z}) = 1))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.IsASM` (`✓ std3`).

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Section 2 (p. 3): “An ASM is a square ASR whose rows and columns each sum to 1.”

**Definition 1.9 (Contains312).**

$$\begin{aligned}\forall (m : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , \operatorname{Contains312} (m := m) M : \operatorname{Prop}\\\forall (m : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , \operatorname{Contains312} (m := m) M \Leftrightarrow (\exists (i_{1} i_{2} i_{3} j_{1} j_{2} j_{3} : \operatorname{Fin} m) , i_{1} < i_{2} \land i_{2} < i_{3} \land j_{1} < j_{2} \land j_{2} < j_{3} \land M i_{1} j_{3} = 1 \land M i_{2} j_{1} = 1 \land M i_{3} j_{2} = 1)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.Contains312` (`✓ std3`).

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Section 2 (p. 3): “We say that M contains a pattern π if there exist 1 ≤ i₁ < · · · < iₙ ≤ m and 1 ≤ j₁ < · · · < jₙ ≤ m such that Mᵢ₁,ⱼπ(1) = · · · = Mᵢₙ,ⱼπ(n) = 1.” The binding convention specializes π to 312 with zero-based Fin indices.

**Definition 1.10 (ExtAvoids312).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{ExtAvoids312} (r := r) (k := k) R : \operatorname{Prop}\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{ExtAvoids312} (r := r) (k := k) R \Leftrightarrow (\exists (m : \mathbb{N}) (\operatorname{hr} : r \le m) (\operatorname{hk} : k \le m) (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , \operatorname{IsASM} M \land \neg \operatorname{Contains312} M \land (\forall i j , M (\operatorname{Fin} . \operatorname{castLE} \operatorname{hr} i) (\operatorname{Fin} . \operatorname{castLE} \operatorname{hk} j) = R i j))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.ExtAvoids312` (`✓ std3`).

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The source says: “An ASR is said to extendably avoid a pattern if there exists an extension of the ASR to a square ASM that avoids the pattern.” (p. 3). The extension contains the given matrix as its top-left corner and may have any size.

**Definition 1.11 (nonemptyRows).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{nonemptyRows} (r := r) (k := k) R : \mathbb{N}\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{nonemptyRows} (r := r) (k := k) R = ((\operatorname{univ} . \operatorname{filter} (\operatorname{fun} i : \operatorname{Fin} r \mapsto \exists j : \operatorname{Fin} k , R i j \neq 0)) . \operatorname{card})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.nonemptyRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.12 (S).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , S r k d : \mathbb{N}\\\forall (r k d : \mathbb{N}) , S r k d = (\operatorname{Nat} . \operatorname{card} \left\{R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType} | \operatorname{IsASR} R \land \operatorname{ExtAvoids312} R \land \operatorname{nonemptyRows} R = d\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.S` (`✓ std3`).

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The count is Nat.card of the subtype of ASRs with the stated existential extension and exactly d nonempty rows (Section 2, p. 3).

**Lemma 1.13 (singleton_line).**

$$\forall (n : \mathbb{N}) , \forall (p : \operatorname{Fin} n) , \operatorname{Alternates} (\operatorname{fun} j \mapsto \operatorname{if} p = j \operatorname{then} 1 \operatorname{else} 0) \land \operatorname{StartsOne} (\operatorname{fun} j \mapsto \operatorname{if} p = j \operatorname{then} 1 \operatorname{else} 0) \land \operatorname{EndsOne} (\operatorname{fun} j \mapsto \operatorname{if} p = j \operatorname{then} 1 \operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.singleton_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.14 (S_zero).**

$$\forall (r k : \mathbb{N}) , S r k 0 = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.S_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.15 (row_has_one).**

$$\forall (m : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , (\operatorname{IsASM} M) \to \forall (i : \operatorname{Fin} m) , \exists j , M i j = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.row_has_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.16 (empty_row_extension_one).**

$$\forall (r k m : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hr} : r \le m) , \forall (\operatorname{hk} : k \le m) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , (\operatorname{IsASM} M) \to (\forall i j , M (\operatorname{Fin} . \operatorname{castLE} \operatorname{hr} i) (\operatorname{Fin} . \operatorname{castLE} \operatorname{hk} j) = R i j) \to \forall (i_{0} : \operatorname{Fin} r) , (\forall j , R i_{0} j = 0) \to \exists j : \operatorname{Fin} m , k \le j . \operatorname{val} \land M (\operatorname{Fin} . \operatorname{castLE} \operatorname{hr} i_{0}) j = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.empty_row_extension_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.17 (no12_below_empty).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{ExtAvoids312} R) \to \forall (i_{0} i_{1} i_{2} : \operatorname{Fin} r) , \forall (j_{1} j_{2} : \operatorname{Fin} k) , (i_{0} < i_{1}) \to (i_{1} < i_{2}) \to (j_{1} < j_{2}) \to (\forall j , R i_{0} j = 0) \to \neg (R i_{1} j_{1} = 1 \land R i_{2} j_{2} = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.no12_below_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.18 (prefix_line).**

$$\forall (n p : \mathbb{N}) , \forall (\operatorname{hp} : p \le n) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to \operatorname{Alternates} (\operatorname{fun} i : \operatorname{Fin} p \mapsto a (\operatorname{Fin} . \operatorname{castLE} \operatorname{hp} i)) \land \operatorname{StartsOne} (\operatorname{fun} i : \operatorname{Fin} p \mapsto a (\operatorname{Fin} . \operatorname{castLE} \operatorname{hp} i))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.prefix_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.19 (topRows).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (p : \mathbb{N}) , \forall (\operatorname{hp} : p \le r) , \operatorname{topRows} (r := r) (k := k) (p := p) R \operatorname{hp} : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} k) \operatorname{SignType}\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (p : \mathbb{N}) , \forall (\operatorname{hp} : p \le r) , \operatorname{topRows} (r := r) (k := k) (p := p) R \operatorname{hp} = (\operatorname{fun} i j \mapsto R (\operatorname{Fin} . \operatorname{castLE} \operatorname{hp} i) j)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.topRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.20 (topRows_isASR).**

$$\forall (r k p : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hp} : p \le r) , (\operatorname{IsASR} R) \to \operatorname{IsASR} (\operatorname{topRows} R \operatorname{hp})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.topRows_isASR` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.21 (topRows_extAvoids312).**

$$\forall (r k p : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hp} : p \le r) , (\operatorname{ExtAvoids312} R) \to \operatorname{ExtAvoids312} (\operatorname{topRows} R \operatorname{hp})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.topRows_extAvoids312` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.22 (LineState).**

$$\begin{aligned}\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{LineState} (n := n) a : \operatorname{Prop}\\\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \operatorname{LineState} (n := n) a \Leftrightarrow (((\forall i , a i = 0) \land (\sum_{i} (a i : \mathbb{Z})) = 0) \lor \exists x , a x \neq 0 \land (\forall y , x < y \to a y = 0) \land (\sum_{i} (a i : \mathbb{Z})) = \operatorname{if} a x = 1 \operatorname{then} 1 \operatorname{else} 0)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.LineState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.23 (alternating_line_state).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to \operatorname{LineState} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.alternating_line_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.24 (asr_row_sum).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \forall (i : \operatorname{Fin} r) , (\sum_{j} (R i j : \mathbb{Z})) = \operatorname{if} \exists j , R i j \neq 0 \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.25 (asr_row_sum_one_iff).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \forall (i : \operatorname{Fin} r) , (\sum_{j} (R i j : \mathbb{Z})) = 1 \Leftrightarrow \exists j , R i j \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_row_sum_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.26 (one_before_minus).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{StartsOne} a) \to \forall (x : \operatorname{Fin} n) , (a x = - 1) \to \exists y , y < x \land a y = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.one_before_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.27 (one_after_minus_of_ends).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{EndsOne} a) \to \forall (x : \operatorname{Fin} n) , (a x = - 1) \to \exists y , x < y \land a y = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.one_after_minus_of_ends` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.28 (line_sum_one_ends_one).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to ((\sum_{i} (a i : \mathbb{Z})) = 1) \to \operatorname{EndsOne} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.line_sum_one_ends_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.29 (asm_column_ends_one).**

$$\forall (m : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , (\operatorname{IsASM} M) \to \forall (j : \operatorname{Fin} m) , \operatorname{EndsOne} (\operatorname{fun} i \mapsto M i j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asm_column_ends_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.30 (asr_row_minus_unique).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{ExtAvoids312} R) \to \forall (i : \operatorname{Fin} r) , \forall (j_{1} j_{2} : \operatorname{Fin} k) , (R i j_{1} = - 1) \to (R i j_{2} = - 1) \to j_{1} = j_{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_row_minus_unique` (`✓ std3`). ∎

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Lemma 4.1 (p. 6): an extendably 312-avoiding ASR has at most one −1 in each row.

**Lemma 1.31 (asr_column_minus_unique).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{ExtAvoids312} R) \to \forall (j : \operatorname{Fin} k) , \forall (i_{1} i_{2} : \operatorname{Fin} r) , (R i_{1} j = - 1) \to (R i_{2} j = - 1) \to i_{1} = i_{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_column_minus_unique` (`✓ std3`). ∎

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Lemma 4.1 (p. 6): an extendably 312-avoiding ASR has at most one −1 in each column.

**Lemma 1.32 (minus_between_ones).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to \forall (x y : \operatorname{Fin} n) , (x < y) \to (a x = 1) \to (a y = 1) \to \exists z , x < z \land z < y \land a z = - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.minus_between_ones` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.33 (asr_first_col_not_minus).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (0 < k) \to \forall (i : \operatorname{Fin} r) , R i \langle 0\rangle \neq - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_first_col_not_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.34 (asr_first_col_one_unique).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (a b : \operatorname{Fin} r) , (R a \langle 0 , \operatorname{hk}\rangle = 1) \to (R b \langle 0 , \operatorname{hk}\rangle = 1) \to a = b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_first_col_one_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.35 (line_no_minus_singleton).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to (\forall x , a x \neq - 1) \to \forall (p : \operatorname{Fin} n) , (a p = 1) \to \forall x , a x = \operatorname{if} x = p \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.line_no_minus_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.36 (asr_first_row_not_minus).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (0 < r) \to \forall (c : \operatorname{Fin} k) , R \langle 0\rangle c \neq - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_first_row_not_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.37 (asr_first_row_singleton).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \forall (\operatorname{hr} : 0 < r) , (\exists c , R \langle 0 , \operatorname{hr}\rangle c \neq 0) \to \exists p , \forall c , R \langle 0\rangle c = \operatorname{if} c = p \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_first_row_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.38 (three_sign_line).**

$$\forall (n : \mathbb{N}) , \forall (x z y : \operatorname{Fin} n) , (x < z) \to (z < y) \to \operatorname{let} a := \operatorname{fun} w \mapsto \operatorname{if} w = x \operatorname{then} (1 : \operatorname{SignType}) \operatorname{else} \operatorname{if} w = z \operatorname{then} - 1 \operatorname{else} \operatorname{if} w = y \operatorname{then} 1 \operatorname{else} 0 ; \operatorname{Alternates} a \land \operatorname{StartsOne} a \land \operatorname{EndsOne} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.three_sign_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.39 (emptyRows).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{emptyRows} (r := r) (k := k) R : \operatorname{Finset} (\operatorname{Fin} r)\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{emptyRows} (r := r) (k := k) R = (\operatorname{univ} . \operatorname{filter} (\operatorname{fun} i : \operatorname{Fin} r \mapsto \forall j : \operatorname{Fin} k , R i j = 0))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.emptyRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.40 (colSum).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (j : \operatorname{Fin} k) , \operatorname{colSum} (r := r) (k := k) R j : \mathbb{Z}\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (j : \operatorname{Fin} k) , \operatorname{colSum} (r := r) (k := k) R j = (\sum_{i} (R i j : \mathbb{Z}))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.colSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.41 (deficientColumns).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{deficientColumns} (r := r) (k := k) R : \operatorname{Finset} (\operatorname{Fin} k)\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{deficientColumns} (r := r) (k := k) R = (\operatorname{univ} . \operatorname{filter} (\operatorname{fun} j : \operatorname{Fin} k \mapsto \operatorname{colSum} R j = 0))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.deficientColumns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.42 (mem_emptyRows).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (i : \operatorname{Fin} r) , i \in \operatorname{emptyRows} R \Leftrightarrow \forall j , R i j = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.mem_emptyRows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.43 (mem_deficientColumns).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (j : \operatorname{Fin} k) , j \in \operatorname{deficientColumns} R \Leftrightarrow \operatorname{colSum} R j = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.mem_deficientColumns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.44 (asr_col_sum).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \forall (j : \operatorname{Fin} k) , \operatorname{colSum} R j = 0 \lor \operatorname{colSum} R j = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_col_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.45 (asr_total_sum).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\sum_{i} \sum_{j} (R i j : \mathbb{Z})) = \operatorname{nonemptyRows} R$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_total_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.46 (emptyRows_balance).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{emptyRows} R) . \operatorname{card} + \operatorname{nonemptyRows} R = r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.emptyRows_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.47 (deficientColumns_balance).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{deficientColumns} R) . \operatorname{card} + \operatorname{nonemptyRows} R = k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.deficientColumns_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.48 (nonemptyRows_le_rows).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{nonemptyRows} R \le r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.nonemptyRows_le_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.49 (nonemptyRows_le_columns).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \operatorname{nonemptyRows} R \le k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.nonemptyRows_le_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.50 (balanced_column_sum).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{nonemptyRows} R = k) \to \forall (j : \operatorname{Fin} k) , \operatorname{colSum} R j = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.balanced_column_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.51 (prefix_sum_as_filter).**

$$\forall (n p : \mathbb{N}) , \forall (\operatorname{hp} : p \le n) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\sum_{i : \operatorname{Fin} p} (a (\operatorname{Fin} . \operatorname{castLE} \operatorname{hp} i) : \mathbb{Z})) = \sum_{i \in \operatorname{univ} . \operatorname{filter} (\operatorname{fun} i : \operatorname{Fin} n \mapsto i . \operatorname{val} < p)} (a i : \mathbb{Z})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.prefix_sum_as_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.52 (one_after_zero_prefix).**

$$\forall (n p : \mathbb{N}) , \forall (\operatorname{hp} : p \le n) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , ((\sum_{i} (a i : \mathbb{Z})) = 1) \to ((\sum_{i : \operatorname{Fin} p} (a (\operatorname{Fin} . \operatorname{castLE} \operatorname{hp} i) : \mathbb{Z})) = 0) \to \exists i , p \le i . \operatorname{val} \land a i = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.one_after_zero_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.53 (deficient_column_extension_one).**

$$\forall (r k m : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (\operatorname{hr} : r \le m) , \forall (\operatorname{hk} : k \le m) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \operatorname{SignType}) , (\operatorname{IsASM} M) \to (\forall i j , M (\operatorname{Fin} . \operatorname{castLE} \operatorname{hr} i) (\operatorname{Fin} . \operatorname{castLE} \operatorname{hk} j) = R i j) \to \forall (j : \operatorname{Fin} k) , ((\sum_{i} (R i j : \mathbb{Z})) = 0) \to \exists i : \operatorname{Fin} m , r \le i . \operatorname{val} \land M i (\operatorname{Fin} . \operatorname{castLE} \operatorname{hk} j) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.deficient_column_extension_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.Alternates`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.Contains312`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.EndsOne`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.ExtAvoids312`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.IsASM`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.IsASR`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.LineState`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.S`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.S_zero`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.StartsOne`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.alternating_line_state`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asm_column_ends_one`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_col_sum`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_column_minus_unique`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_first_col_not_minus`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_first_col_one_unique`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_first_row_not_minus`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_first_row_singleton`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_row_minus_unique`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_row_sum`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_row_sum_one_iff`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.asr_total_sum`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.balanced_column_sum`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.colSum`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.deficientColumns`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.deficientColumns_balance`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.deficient_column_extension_one`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.emptyRows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.emptyRows_balance`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.empty_row_extension_one`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.ends_embed`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.line_embed`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.line_no_minus_singleton`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.line_sum_one_ends_one`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.mem_deficientColumns`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.mem_emptyRows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.minus_between_ones`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.no12_below_empty`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.nonemptyRows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.nonemptyRows_le_columns`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.nonemptyRows_le_rows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.one_after_minus_of_ends`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.one_after_zero_prefix`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.one_before_minus`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.prefix_line`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.prefix_sum_as_filter`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.row_has_one`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.singleton_line`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.sum_embed`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.three_sign_line`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.topRows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.topRows_extAvoids312`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SignLines.topRows_isASR`
