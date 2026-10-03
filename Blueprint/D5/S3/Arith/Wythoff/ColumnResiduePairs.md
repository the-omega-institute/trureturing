# Wythoff column residue pairs

## Abstract

The first two Wythoff columns attain all residue pairs modulo every positive integer.

Write phi=(1+sqrt(5))/2. Rows and columns start at one. The array W has W(n,0)=floor(n phi), W(n,1)=floor(floor(n phi) phi), W(n,2)=floor(floor(n phi) phi^2), and W(n,k+2)=W(n,k+1)+W(n,k) for k>=1. Its first row is 1,2,3,5,... . Let R(m) be the image of positive row indices under n -> (W(n,1) mod m,W(n,2) mod m). Let w(m,n,k) denote W(n,k) reduced to ZMod(m).

**Theorem 1.1 (All-modulus residue coverage).**

$$\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(ncard\left(R\left(m\right)\right) = m^{2} \land \left(\forall a \in ZMod\left(m\right), b \in ZMod\left(m\right),\; \exists n \in \mathbb{N},\; 1 \le n \land \left(w\left(m, n, 1\right) = a \land w\left(m, n, 2\right) = b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Wythoff/ColumnResiduePairs.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a035513-wythoff-column-residue-pairs` (proved) by `D5/S3/Arith/Wythoff/ColumnResiduePairs.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a035513-wythoff-column-residue-pairs","declaration_gid":"D5/S3/Arith/Wythoff/ColumnResiduePairs.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling (2025). *OEIS A035513: Wythoff array read by falling antidiagonals*. URL: <https://oeis.org/A035513>.

*Commentary.*

The two floor expressions simplify to floor(n phi)+n-1 and 2 floor(n phi)+n-1. Given residues a,b, choose r=2a-b and s=b-a. Along positive indices n=r+1+mk, irrational rotation on the circle of circumference m is dense. An open interval between s and s+1 therefore supplies floor(n phi)=s modulo m, and the linear formulas give a,b. The image is the full product, which has m^2 elements. The modulus-one case strengthens Kimberling's m>=2 assertion.

## References

- Truth anchor: `D5/S3/Arith/Wythoff/ColumnResiduePairs.result`
