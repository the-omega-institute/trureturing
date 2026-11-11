# OEIS A233154

## Abstract

The literal 7-column count obeys a recurrence determined by its finite row quotient.

**Definition 1.1 (T7).**

$$\forall n \in \operatorname{Nat},\; T7\left(n\right) = Finset.card\left(Finset.filter\left((\lambda f: Fin\left(n\right) \times Fin\left(7\right) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.T7` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

Every labelled function satisfying the two bond conditions is counted.

**Definition 1.2 (classes).**

$$(classes: Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to Fin\left(16\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.classes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

The complete nested lookup table on the 7 row coordinates, including its zero entries.

**Definition 1.3 (classify).**

$$\forall r \in Row\left(7\right),\; classify\left(r\right) = classes\left(r\left(0\right), r\left(1\right), r\left(2\right), r\left(3\right), r\left(4\right), r\left(5\right), r\left(6\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.classify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

The finite decision tree assigns the successor class of a row.

**Definition 1.4 (quotient).**

$$quotient = ![![5, 5, 3, 3, 4, 4, 2, 2, 3, 3, 3, 3, 1, 1, 0, 0], ![4, 4, 3, 3, 4, 4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1], ![3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 2, 2, 0, 0], ![1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2], ![4, 4, 2, 2, 4, 4, 2, 2, 3, 3, 1, 1, 1, 1, 0, 0], ![4, 4, 2, 2, 4, 4, 2, 2, 2, 2, 3, 3, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 1, 1], ![0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2, 2, 3, 3], ![3, 3, 3, 3, 3, 3, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0], ![2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 1, 1, 1], ![4, 4, 3, 3, 2, 2, 1, 1, 3, 3, 3, 3, 2, 2, 0, 0], ![2, 2, 3, 3, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2], ![2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 0, 0], ![2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2], ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 3, 3], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.quotient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

The quotient entry counts legal compatible successors in each class.

**Definition 1.5 (weights).**

$$weights = ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

The weights count legal rows in each class.

**Definition 1.6 (codes).**

$$codes = [0, 1, 3, 5, 9, 10, 16, 17, 27, 28, 30, 32, 48, 50, 52, 53, 81, 82, 84, 86, 90, 91, 97, 98, 144, 145, 151, 152, 156, 158, 160, 161, 243, 244, 246, 248, 252, 253, 259, 260, 270, 271, 273, 275, 291, 293, 295, 296, 432, 433, 435, 437, 453, 455, 457, 458, 468, 469, 475, 476, 480, 482, 484, 485, 729, 730, 732, 734, 738, 739, 745, 746, 756, 757, 759, 761, 777, 779, 781, 782, 810, 811, 813, 815, 819, 820, 826, 827, 873, 874, 880, 881, 885, 887, 889, 890, 1296, 1297, 1299, 1301, 1305, 1306, 1312, 1313, 1359, 1360, 1366, 1367, 1371, 1373, 1375, 1376, 1404, 1405, 1407, 1409, 1425, 1427, 1429, 1430, 1440, 1441, 1447, 1448, 1452, 1454, 1456, 1457, 1701, 1702, 1704, 1706, 1710, 1711, 1717, 1718, 1728, 1729, 1731, 1733, 1749, 1751, 1753, 1754, 1890, 1891, 1893, 1895, 1911, 1913, 1915, 1916, 1926, 1927, 1933, 1934, 1938, 1940, 1942, 1943, 2025, 2026, 2028, 2030, 2034, 2035, 2041, 2042, 2088, 2089, 2095, 2096, 2100, 2102, 2104, 2105, 2133, 2134, 2136, 2138, 2154, 2156, 2158, 2159, 2169, 2170, 2176, 2177, 2181, 2183, 2185, 2186]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.codes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

The list contains every legal row code once.

**Definition 1.7 (classCount).**

$$\forall r \in Row\left(7\right),\; \forall s \in Fin\left(16\right),\; classCount\left(r, s\right) = List.sum\left(List.map\left((\lambda c: Fin\left(2187\right) \mapsto (\operatorname{if} (compatible\left(r, decode\left(7, c\right)\right)) \land (classify\left(decode\left(7, c\right)\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0)), codes\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

The sum counts compatible legal successors in one destination class.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.T7`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.classes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.classify`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.codes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.quotient`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
