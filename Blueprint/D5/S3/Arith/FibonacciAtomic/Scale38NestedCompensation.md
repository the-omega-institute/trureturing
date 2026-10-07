# Nested Compensation

## Abstract

Nested left combs share a fixed root compensation position and a literal raw scan.

**Theorem 1.1 (Common leaves of nonconflicting trees).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.agree`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.agree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P and Q be nonconflicting trees and u an address. If both reports readout(u,P) and readout(u,Q) have charge chi equal to zero, so that u is a leaf of both trees, then the two reports are equal: a common leaf carries the same alpha or beta label in both trees.

**Theorem 1.2 (A split of a nonconflicting family charges some member).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.root_excess`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.root_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a finite family of pairwise nonconflicting trees, S a survivor set with at least two members, and r a recursive response recipe on S. Then some member of S has response excess gain(r,i) at least one. Indeed, if every member had zero excess, every member would report a leaf at the first requested address; common leaves carry equal reports, so that address would not split S.

**Theorem 1.3 (Splitting the scan range at a prefix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.divide`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.divide` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural numbers t <= k, the list 0,1,...,k is the list 0,...,t-1, followed by t, followed by the consecutive list t+1,...,k.

**Theorem 1.4 (Complete sources and exact requested-address bills).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write (s,t) for ordered tree pairing. Let E=(beta,alpha), A=(E,beta), C=(A,E), and B=(C,A). The tree H_r is the right comb of r copies of A ending in C; h_r is the right comb of r alpha leaves ending in beta. The comb G_(k,j) changes its j-th A slot to B. The sources are P_0=(H_k,B), X_j=(G_(k,j),A), and Y_i=(H_i,(H_(k-i),A)), for 1 <= j <= k and 0 <= i < k.

Their complete preimages are (h_k,E), (g_(k,j),alpha), and (h_i,(h_(k-i),alpha)), respectively. Here g_(k,j) has k left slots ending in beta, with E at slot j and alpha at every other slot.

For every positive integer k, the baseline, the k enlarged-slot rows, and the k contracted-left-comb rows are distinct actual third substitution images. Each has the stated unique complete preimage, with composition (k+1,2). Their image composition is (k+5,2k+8), with 3k+13 leaves. Every pair is nonconflicting, including pairs whose left combs end at different depths.

The scan requests L followed by t right turns and LLR, for t from zero through k. Alpha replies continue the scan. A branch selects X_(t+1) when t < k; an absent reply at t greater than zero selects Y_(t-1). All alpha replies select the baseline. The complete leaf test uses shortlex order, with left before right at equal lengths. Every other reply starts total tree acquisition. A selection always starts a complete labelled-leaf test, with a mismatch also starting total acquisition.

For every prefix length t from zero through k+1, compatibility with all earlier alpha scan reports holds exactly for the baseline and rows whose exit position is at least t. In the one-based slot names, these are X_j with j >= t+1 and Y_i with i >= max(0,t-1), as well as P_0. At t=k+1 only P_0 remains. The family has exactly 2k+1 members, and all scan addresses are distinct.

The same controller terminates and decides third-image membership for every finite input tree. On the baseline its distinct requested addresses are exactly the leaves. On an enlarged-slot or contraction row they are the leaves together with its single branch or absent exit address. The earlier scan addresses are actual alpha leaves of that input, and the exit address is not a leaf. Thus the baseline costs 3k+13 and every exceptional row costs 3k+14. A fresh outer cache stores only requested addresses and their truthful replies, contains no duplicate address, and pays the same distinct-address set. Every globally correct original strategy costs at least 3k+14 on some row, so the deterministic common cost is exactly 3k+14.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.agree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.divide`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.root_excess`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion](ActualCoarseReadoutCompletion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization](FiniteHereditaryPatternRealization.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum](FourExitRawEndpointSpectrum.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](SourceTransportCentralizer.md)
