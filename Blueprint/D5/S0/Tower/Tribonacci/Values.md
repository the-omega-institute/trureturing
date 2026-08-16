# Tribonacci Values

## Abstract

Admissible Tribonacci words acquire real values from the Tribonacci constant.

The Tribonacci constant is constructed as a real root between one and two of x cubed equals x squared plus x plus one. A word is read from left to right with weights t^-1 through t^-Q.

**Definition 1.1 (Tribonacci constant).**

Lean statement: `D5/S0/Tower/Tribonacci/Values.tribonacciConstant`

*Formalization.* `D5/S0/Tower/Tribonacci/Values.tribonacciConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Intermediate value on the interval from one to two supplies the root; the accompanying bounds and cubic equation are kernel-proved.

**Definition 1.2 (Tribonacci name value).**

Lean statement: `D5/S0/Tower/Tribonacci/Values.tribonacciNameValue`

*Formalization.* `D5/S0/Tower/Tribonacci/Values.tribonacciNameValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each true position contributes the corresponding negative power of the Tribonacci constant, giving the geometric value of an admissible name.

**Definition 1.3 (Indexed Tribonacci name value).**

Lean statement: `D5/S0/Tower/Tribonacci/Values.indexedNameValue`

*Formalization.* `D5/S0/Tower/Tribonacci/Values.indexedNameValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical prefix order splits each nontrivial level into zero, one-zero, and one-one-zero blocks matching the three-term count.

**Definition 1.4 (Ordered small-level gap validation).**

Lean statement: `D5/S0/Tower/Tribonacci/Values.adjacentNameValueGaps`

*Formalization.* `D5/S0/Tower/Tribonacci/Values.adjacentNameValueGaps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Executable examples in the Lean module compute every adjacent gap with multiplicity and order for levels two, three, and four before the general spectrum theorem is invoked.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/Values.adjacentNameValueGaps`
- Truth anchor: `D5/S0/Tower/Tribonacci/Values.indexedNameValue`
- Truth anchor: `D5/S0/Tower/Tribonacci/Values.tribonacciConstant`
- Truth anchor: `D5/S0/Tower/Tribonacci/Values.tribonacciNameValue`
- Dependency: [D5/S0/Tower/Tribonacci/Names](Names.md)
