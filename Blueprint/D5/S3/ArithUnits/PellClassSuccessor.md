# Wu's Pell-Class Successor Criterion

## Abstract

The least square partner and integral-unit classes of the norm-(k^2+1) equation.

**Definition 1.1 (The integer parameter).**

$$\forall k \in \mathrm{Nat},\; \operatorname{Discriminant}\left(k\right) = \operatorname{IntOfNat}\left(k\right)^{2} + 1$$

*Formalization.* `D5/S3/ArithUnits/PellClassSuccessor.Discriminant` (`✓ std3`).

*Citation.* Chai Wah Wu (2026). *OEIS A399755: Numbers k such that the generalized Pell equation x^2-(k^2+1)*(y^2+1) = 0 has more than one fundamental solution in (x, y).*. URL: <https://oeis.org/A399755>.

*Commentary.*

The parameter k is a natural number, and Discriminant(k) is an integer. IntOfNat denotes the canonical inclusion of natural numbers into the integers. The defining formula applies to every natural k; positivity is a hypothesis of the final statement.

**Definition 1.2 (Integral solutions of the generalized Pell equation).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathbb{Z}, y \in \mathbb{Z},\; \operatorname{Sol}\left(k, x, y\right) \Leftrightarrow x^{2} - \operatorname{Discriminant}\left(k\right) \cdot y^{2} = \operatorname{Discriminant}\left(k\right)$$

*Formalization.* `D5/S3/ArithUnits/PellClassSuccessor.Sol` (`✓ std3`).

*Citation.* Chai Wah Wu (2026). *OEIS A399755: Numbers k such that the generalized Pell equation x^2-(k^2+1)*(y^2+1) = 0 has more than one fundamental solution in (x, y).*. URL: <https://oeis.org/A399755>.

*Commentary.*

Sol(k,x,y) expresses the equation in the A399755 name, with its right-hand side written as Discriminant(k). Both coordinates range over all integers. There is no primitive-solution or squarefree-parameter restriction.

**Definition 1.3 (Equivalence under integral norm-one units).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathbb{Z}, y \in \mathbb{Z}, r \in \mathbb{Z}, s \in \mathbb{Z},\; \operatorname{SameClass}\left(k, x, y, r, s\right) \Leftrightarrow \left(\exists u \in \mathbb{Z}, v \in \mathbb{Z},\; u^{2} - \operatorname{Discriminant}\left(k\right) \cdot v^{2} = 1 \land \left(x = r \cdot u + \operatorname{Discriminant}\left(k\right) \cdot s \cdot v \land y = r \cdot v + s \cdot u\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/PellClassSuccessor.SameClass` (`✓ std3`).

*Citation.* John P. Robertson (2004). *Solving the generalized Pell equation x^2 - Dy^2 = N*. URL: <https://web.archive.org/web/20160323033128id_/http://www.jpr2718.org/pell.pdf>.

*Commentary.*

On solutions of the same generalized Pell equation, SameClass is the integral-unit relation of the section on the structure of solutions, pages 12 through 14. The unit coordinates u and v are integers and their norm is one. In particular, u=-1 and v=0 are allowed, so simultaneous negation preserves the class. The relation does not identify arbitrary independent sign changes, and does not enlarge the units to fractional coordinates in a maximal order. SameClass itself records the unit action; the Sol conditions are supplied explicitly in MultipleClasses.

**Definition 1.4 (More than one generalized solution class).**

$$\forall k \in \mathrm{Nat},\; \operatorname{MultipleClasses}\left(k\right) \Leftrightarrow \left(\exists x \in \mathbb{Z}, y \in \mathbb{Z}, r \in \mathbb{Z}, s \in \mathbb{Z},\; \operatorname{Sol}\left(k, x, y\right) \land \left(\operatorname{Sol}\left(k, r, s\right) \land \left(\neg \operatorname{SameClass}\left(k, x, y, r, s\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/PellClassSuccessor.MultipleClasses` (`✓ std3`).

*Citation.* Chai Wah Wu (2026). *OEIS A399755: Numbers k such that the generalized Pell equation x^2-(k^2+1)*(y^2+1) = 0 has more than one fundamental solution in (x, y).*. URL: <https://oeis.org/A399755>.

*Commentary.*

A399755 membership means that two integral solutions lie in different classes under SameClass. The classical convention selects one fundamental representative per generalized solution class. This is distinct from the fundamental positive solution of the norm-one equation. The versioned SymPy diop_DN docstring's one-tuple-per-class convention is a semantic reference for the source program; no execution of that program is a mathematical premise. Membership concerns the integer k itself, not the kth listed value of A399755.

**Definition 1.5 (The least larger square partner).**

$$\forall k \in \mathrm{Nat}, m \in \mathrm{Nat},\; \operatorname{NextSquarePartner}\left(k, m\right) \Leftrightarrow \left(k < m \land \left(\operatorname{IsSquare}\left(\left(k^{2} + 1\right) \cdot \left(m^{2} + 1\right)\right) \land \left(\forall n \in \mathrm{Nat},\; k < n \Rightarrow \left(\operatorname{IsSquare}\left(\left(k^{2} + 1\right) \cdot \left(n^{2} + 1\right)\right) \Rightarrow m \le n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/PellClassSuccessor.NextSquarePartner` (`✓ std3`).

*Citation.* Chai Wah Wu (2026). *OEIS A399755: Numbers k such that the generalized Pell equation x^2-(k^2+1)*(y^2+1) = 0 has more than one fundamental solution in (x, y).*. URL: <https://oeis.org/A399755>.

*Commentary.*

The companion A399491 definition selects the least natural m greater than k for which the displayed product is a square. IsSquare is the square predicate on natural numbers. The universal condition compares m with every larger candidate n satisfying the same square predicate. Thus the definition includes both admissibility and the entire minimum condition; existence is asserted separately in the final statement.

**Theorem 1.6 (The least-partner existence and strict cubic equivalence).**

$$\forall k \in \mathrm{Nat},\; 0 < k \Rightarrow \left(\exists m \in \mathrm{Nat},\; \operatorname{NextSquarePartner}\left(k, m\right) \land \left(m < 4 \cdot k^{3} + 3 \cdot k \Leftrightarrow \operatorname{MultipleClasses}\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/PellClassSuccessor.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a399755-pell-class-successor` (proved) by `D5/S3/ArithUnits/PellClassSuccessor.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a399755-pell-class-successor","declaration_gid":"D5/S3/ArithUnits/PellClassSuccessor.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu (2026). *OEIS A399755: Numbers k such that the generalized Pell equation x^2-(k^2+1)*(y^2+1) = 0 has more than one fundamental solution in (x, y).*. URL: <https://oeis.org/A399755>.

*Acknowledgement.* John P. Robertson (2004). *Solving the generalized Pell equation x^2 - Dy^2 = N*. URL: <https://web.archive.org/web/20160323033128id_/http://www.jpr2718.org/pell.pdf>.

*Commentary.*

The statement concerns every positive natural k. It asserts the existence of a least square partner m and identifies the strict inequality below the cubic bound with the presence of more than one integral-unit class. Both directions use the same least partner. The named source conjecture supplies the equivalence to be addressed, while the existential quantifier makes explicit the totality implicit in A399491(k). Classical class terminology supplies the meaning of membership, not a proof of this uniform source-and-order assertion. The proof constructs the cubic endpoint partner, characterizes multiple classes by a norm-D solution whose first coordinate is not divisible by D, and uses integer descent under an explicit norm-one unit to obtain the strict interval. The least-witness principle supplies the full minimum condition.

## References

- Truth anchor: `D5/S3/ArithUnits/PellClassSuccessor.Discriminant`
- Truth anchor: `D5/S3/ArithUnits/PellClassSuccessor.MultipleClasses`
- Truth anchor: `D5/S3/ArithUnits/PellClassSuccessor.NextSquarePartner`
- Truth anchor: `D5/S3/ArithUnits/PellClassSuccessor.SameClass`
- Truth anchor: `D5/S3/ArithUnits/PellClassSuccessor.Sol`
- Truth anchor: `D5/S3/ArithUnits/PellClassSuccessor.result`
