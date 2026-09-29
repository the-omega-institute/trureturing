# A Surjective Column and Sharp Response Width

## Abstract

One surjective column gives the optimal coefficient-one width bound and the sharp uniform real exponent.

Let r and h be natural numbers with r>=1 and 0<=h<=r. For each 1<=i<=r, let t_i be a Boolean coordinate and d_i a coordinate in an arbitrary finite nonempty set D_i. There are two further coordinates a in A and b in B. All 2r+2 coordinates are distinct, and inputs range over their full independent product. The symbol mathbb B denotes the Boolean set; the unadorned B denotes the alphabet of b. The task is F(t,a,b,d)=G(t,psi(a,b)), so the d_i do not affect its value.

Let I be the full set of labels and Omega_Q the product of the alphabets at labels in Q. For a set P of coordinate labels, a prefix assignment x in Omega_P fixes precisely P. Its response R_P(x) is the function y |-> F(x joined with y), where y ranges over the full product of the complementary labelled coordinates. Every prefix at this cut has exactly this same suffix domain. Two prefixes are equivalent exactly when these functions agree on every suffix. The capacity kappa_P(F) is the number of distinct response functions, rather than the number of output values.

$\begin{gathered}R_{P}(x): \omega_{I\setminus P}\to O, y\mapsto F(join(x, y))\\\kappa_{P}(F)=\lvert\{R_{P}(x)\mid x\in\omega_{P}\}\rvert\\W_{F}(e)=\max_{0\leq k\leq2r+2}\kappa_{P_{e}(k)}(F)\end{gathered}$

Positions are numbered from zero. The order pi is (t_1,...,t_h,a,t_(h+1),...,t_r,b,d_1,...,d_r), and rho is (a,b,t_1,d_1,...,t_r,d_r). Thus pos_pi(a)=h, pos_pi(b)=r+1, pos_pi(t_i)=i-1 for i<=h and i otherwise, and pos_pi(d_i)=r+1+i. Also pos_rho(a)=0, pos_rho(b)=1, pos_rho(t_i)=2i, and pos_rho(d_i)=2i+1. For either order eta, P_eta(k) contains the labels whose positions are less than k. Width takes the maximum over every k=0,...,2r+2, including the empty prefix and the final output layer.

Write F_0 for the class of finite sets and F_+ for the finite nonempty sets. The notation D in F_+^r means that each of the r alphabets D_i is finite and nonempty. A map psi:A times B -> Z is written in curried form. The condition psi(A,b_0)=Z refers to one fixed b_0 in B; it makes Z the effective image and imposes no condition on any row or on the other columns. All maps G are total. Write F_o(t,a,b,d)=o for a constant task.

For every natural m>=2, put C_m=(Z/mZ)^(mathbb B^r), take A=B=Z=C_m, and let psi(a,b)=a+b pointwise. Define the Boolean task F_m(t,a,b,d) to be true exactly when (a+b)(t)=0. Both addition slices are surjective. The alphabets D_i remain the same arbitrary fixed sets. Write kappa_eta(m,k) for the actual response capacity of F_m at P_eta(k), and W_m(eta) for its width. For 0<=k<=2r+2, the functions p and q below give every raw layer.

$\begin{gathered}\operatorname{p}\left(r, h, m, k\right)=\begin{cases}2^{k}&k\leq h\\2^{k-1}m^{2^{r-(k-1)}}&h<k\leq r+1\\2&r+1<k\end{cases}\\\operatorname{q}\left(r, m, k\right)=\begin{cases}1&k=0\\m^{2^{r}}&k=1\\2^{2^{r-\lfloor\frac{k-1}{2}\rfloor}}&2\leq k\end{cases}\end{gathered}$

**Theorem 1.1 (Coefficient one, all layer counts, and optimal uniform exponent).**

$$\begin{gathered}\forall r,h \in \mathbb{N}, 1\leq r\land h\leq r\implies\forall D\in\mathcal{F}_{+}^{r},\\(\forall A,B,O \in \mathcal{F}_{+}, \forall Z \in \mathcal{F}_{0}, \forall \psi \in A\to B\to Z, \forall G \in \mathbb{B}^{r}\to Z\to O, \forall b_{0} \in B, \psi(A, b_{0})=Z\implies W_{F}(\rho)\leq W_{F}(\pi)^{2^{h}})\\\land\\(\forall m \in \mathbb{N}, 2\leq m\implies((\forall k \in \mathbb{N}, k\leq2r+2\implies(\kappa_{\pi}(m, k)=\operatorname{p}\left(r, h, m, k\right)\land\kappa_{\rho}(m, k)=\operatorname{q}\left(r, m, k\right)))\land W_{m}(\pi)=2^{h}m^{2^{r-h}}\land W_{m}(\rho)=m^{2^{r}}))\\\land\\(\forall \alpha,C \in \mathbb{R}, \alpha<2^{h}\land0<C\implies\exists m\in\mathbb{N},2\leq m\land CW_{m}(\pi)^{\alpha}<W_{m}(\rho))\\\land\\(\forall A,B \in \mathcal{F}_{+}, \forall Z,O \in \mathcal{F}_{0}, \forall \psi \in A\to B\to Z, \forall o \in O, (W_{F_{o}}(\pi)=1\land W_{F_{o}}(\rho)=1\land\forall C \in \mathbb{R}, W_{F_{o}}(\rho)\leq CW_{F_{o}}(\pi)^{2^{h}}\implies1\leq C))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/SurjectiveColumnSharpWidth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the upper bound, let K_j be the capacity in pi after a and the first j selectors have been read, for h<=j<=r, and let W=W_F(pi). Each K_j is at most W. After a alone in rho, a response is determined by its restrictions at the 2^h assignments of the early selectors. Every restriction is an actual response at the K_h cut. This gives at most K_h^(2^h) possibilities.

Choose a section sigma:Z->A of the surjective column, so psi(sigma(z),b_0)=z. After a,b and j<=h selectors in rho, the residual function is determined by its common-domain restrictions indexed by assignments of the early selectors. Each restriction is obtained from a K_h response by setting b=b_0. Hence the capacity is at most K_h^(2^h), without requiring arbitrary tuples of restrictions to be realizable. For j>h, each residual is instead the restriction at b_0 of a K_j response, giving capacity at most K_j. Reading an irrelevant d_i preserves the capacity: the common suffix projection is surjective and every shorter prefix lifts. The initial capacity is one and the final capacity is the image size. Since W>=1, every layer is bounded by W^(2^h).

In the addition family, after j selectors and a, the response is specified by the selector prefix and its 2^(r-j) relevant entries of a. Different entry vectors are separated by a common suffix with b(t)=-a(t) at a differing entry. Different selector prefixes access different b entries, allowing one zero test to be true and the other false. The resulting count is exactly 2^j m^(2^(r-j)). Before a, the same separation gives 2^j responses. After a,b in rho, every Boolean truth table occurs: independently choose each sum entry to be zero or one. After j selectors, all truth tables on the remaining r-j selectors still occur, giving 2^(2^(r-j)). This also accounts for all intervening irrelevant layers.

The counts 2^j m^(2^(r-j)) decrease as j increases from h to r, because m>=2. The two maxima are therefore exactly the displayed widths. For a smaller real exponent alpha, the ratio W_m(rho)/W_m(pi)^alpha equals 2^(-h alpha) m^(2^r-alpha 2^(r-h)). Its exponent of m is positive precisely when alpha<2^h; increasing m defeats every fixed C>0. The cases h=0, h=r, r=1 and m=2 are included. Finally, a constant task has one response at every cut, so both widths are one and any uniform coefficient at exponent 2^h must be at least one.

## References

- Truth anchor: `D5/S3/Observer/Separation/SurjectiveColumnSharpWidth.result`
