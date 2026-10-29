# Exact Kernel Rigidity on All Native Source Trees

## Abstract

Every Hermitian complex kernel preserved by native Fibonacci substitution and exactly multiplicative on all ordered constructor pairs takes only zero and one.

T is GenealogicalFiberTransport.Source, namely FreeMagma Bool: all nonempty finite ordered binary trees. Alpha is the leaf true, beta is the leaf false, and pair(s,t) is the internal node with ordered children s,t. The native substitution rho sends alpha to beta, beta to pair(beta,alpha), and pair(s,t) to pair(rho(s),rho(t)). No quotient or bound on shape, height or leaf count is imposed. Complex is the complex scalar field and conj is complex conjugation.

**Theorem 1.1 (The Full-Tree Zero-or-One Theorem).**

$$\forall K: T \to (T \to (\operatorname{Complex}\left(\right))), ((\forall s: T, (\forall t: T, (\operatorname{K}\left(t, s\right) = \operatorname{conj}\left(\operatorname{K}\left(s, t\right)\right)))) \implies ((\forall s: T, (\forall t: T, (\operatorname{K}\left(\operatorname{rho}\left(s\right), \operatorname{rho}\left(t\right)\right) = \operatorname{K}\left(s, t\right)))) \implies ((\forall s: T, (\forall t: T, (\forall u: T, (\forall v: T, (\operatorname{K}\left(\operatorname{pair}\left(s, t\right), \operatorname{pair}\left(u, v\right)\right) = \operatorname{K}\left(s, u\right) \cdot \operatorname{K}\left(t, v\right)))))) \implies (\forall s: T, (\forall t: T, ((\operatorname{K}\left(s, t\right) = 0) \lor (\operatorname{K}\left(s, t\right) = 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Kernels/NativeKernelRigidity.kernel_zero_or_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is any total function T to T to Complex. The three premises are Hermitian symmetry for every source pair, preservation of every comparison by rho, and exact constructor multiplicativity for every source quadruple, including different tree shapes and repeated labels. The conclusion holds for every source pair. Positivity, diagonal normalization, faithfulness and regularity are not premises.

Write R(n,u)=rho^n(u), f(n,u)=K(alpha,R(n,u)), and a(n)=f(n,alpha). The alpha-orbit part of SourceTransportCentralizer.source_transport_centralizer gives rho(rho(R(n,alpha)))=pair(rho(R(n,alpha)),R(n,alpha)). It is used only on that orbit. Two transport steps and multiplicativity give a(n)=a(n)*a(n), so the scalar idempotence theorem gives a(n)=0 or a(n)=1.

For arbitrary s,t and every natural n, the same two transport steps give f(n,pair(s,t))=f(n+1,s)*f(n+2,t). The leaf beta gives f(n,beta)=a(n+1). Structural induction on the entire tree u, with n universally quantified, therefore gives f(n,u)=0 or f(n,u)=1.

For beta in the first argument, Hermitian symmetry and transport settle the two leaves. The orbit identity at beta and exact multiplicativity give K(beta,pair(s,t))=K(alpha,s)*K(alpha,rho(t)), also zero or one. Finally, structural induction on the first tree handles all comparisons. A leaf first argument uses these two rows; an internal first argument against a leaf uses Hermitian symmetry; two internal arguments reduce by multiplicativity to comparisons with strictly smaller first trees. Conjugation and multiplication preserve zero and one.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Kernels/NativeKernelRigidity.kernel_zero_or_one`
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](../SourceTransportCentralizer.md)
