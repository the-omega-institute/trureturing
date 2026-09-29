# Sharp Capacities of Smith Coordinate Records

## Abstract

Autonomous reduction forces a lossless supplementary record to distinguish every defective Smith coordinate at full precision.

**Theorem 1.1 (Autonomous records attain the sharp lower bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/RecordCapacity.autonomous_record_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/RecordCapacity.autonomous_record_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural dimension d, a prime p, a d by d integer matrix B, invertible d by d integer matrices U and V, and natural diagonal entries s(i) with UBV = diag(s). Let I contain precisely the indices for which p divides s(i), and put b = |I|. Index positive precision levels by n >= 0, so that level n means reduction modulo p^(n+1). The state space is (Z/p^(n+1) Z)^d, and B acts at that precision. The defective subgroup is obtained by extending an I-indexed vector by zero and applying V.

At each level take an arbitrary finite set R(n) and any function eta(n) from the state space to R(n). Assume each joint map x to (Bx, eta(n)(x)) is injective. Suppose functions rho(n) from R(n+1) to R(n) satisfy rho(n)(eta(n+1)(x)) = eta(n)(x reduced modulo p^(n+1)) for every input. These transition functions receive only the record. Then, for every n, eta(n) is injective on the embedded defective subgroup, and |R(n)| is at least p^((n+1)b).

The bound is attained simultaneously at all levels by the additive record that first applies V inverse and then retains exactly the I coordinates. Its joint map with B is injective, its record set has exactly p^((n+1)b) elements, and coordinatewise natural reduction of these records commutes with reduction of the input. Thus the construction is an autonomous tower.

For the scalar boundary x to px at precision n+1, the kernel has p elements. The highest base-p digit, obtained by dividing the least nonnegative representative by p^n, is a jointly injective record with p possible values. Every supplementary record making the joint encoding injective has at least p values. No function of the highest digit at precision n+2 alone produces the highest digit at precision n+1 for every input. The latter digit can instead be computed by dividing the least nonnegative representative of the fine boundary px by p^(n+1). An autonomous scalar tower requires at least p^(n+1) record values at level n.

For the three-coordinate boundary (x0+2x1, x1+2x2, 2x0+x2), integer invertible row and column changes give diagonal entries (1,1,9). At precision r over the prime 3, its kernel has exactly 3^min(r,2) elements. Among finite supplementary records making the joint encoding injective, the minimum cardinality is 3^min(r,2), and that minimum is attained. An autonomous tower requires at least 3^(n+1) values at level n. Consequently no autonomous tower can have the minimum single-level capacity at every precision: precision three would require at least 27 values while that minimum is 9.

At precision one the boundary vanishes on the defective subgroup. For the induction step, equal records imply equal coarse records and therefore equal reduced defective inputs. Their difference is killed by p at the finer level, hence also by every defective diagonal entry. Joint injectivity now separates the finer inputs. For the attaining record, the omitted diagonal entries are units modulo every power of p, so the boundary recovers all omitted coordinates.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RecordCapacity.autonomous_record_capacity`
