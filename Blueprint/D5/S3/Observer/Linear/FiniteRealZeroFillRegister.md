# Finite Real Zero-Fill Register

## Abstract

A finite real zero-fill register reads every original sign through its horizon.

**Definition 1.1 (Infinite binary inputs).**

$$X:=(\mathbb{N}\to\mathrm{Bool})$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.X` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An input is an arbitrary function from natural times to Bool; no finite encoding or probability measure is imposed.

**Definition 1.2 (The original real sign).**

$$\begin{gathered}\forall b\in \mathrm{Bool},\quad \operatorname{bitSign}(b)=(-1)^{\operatorname{toNat}(b)}\in \mathbb{R}\\{}\operatorname{bitSign}(\operatorname{false})=+1,\quad \operatorname{bitSign}(\operatorname{true})=-1\end{gathered}$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.bitSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original sign is minus one raised to the Boolean natural value: false has sign +1 and true has sign -1.

**Definition 1.3 (The time-indexed original signal).**

$$\forall t\in \mathbb{N}, \forall x\in X,\quad \operatorname{signal}(t,x)=\operatorname{bitSign}(x(t))$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.signal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At time t the signal reads the sign of the original input coordinate x(t).

**Definition 1.4 (The finite real state).**

$$\forall H\in \mathbb{N},\quad \operatorname{State}(H):=(\operatorname{Fin}(H+1)\to\mathbb{R})$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any natural horizon H, the state is the real vector with coordinates Fin(H+1). Its entries are arbitrary real numbers; H=0 still has coordinate zero.

**Definition 1.5 (Initialization from the original input).**

$$\forall H\in \mathbb{N}, \forall x\in X, \forall i\in \operatorname{Fin}(H+1),\quad \operatorname{initState}(H,x)(i)=\operatorname{signal}(i.\operatorname{val},x)$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.initState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Initialize coordinate i with signal(i,x), thereby storing the first H+1 original signs once.

**Definition 1.6 (A fixed linear update with real-zero fill).**

$$\forall H\in \mathbb{N},\quad \begin{gathered}U_{H}:=\operatorname{update}(H)\in \operatorname{Hom}_{\mathbb{R}}(\operatorname{State}(H),\operatorname{State}(H))\\{}\forall q\in \operatorname{State}(H), \forall i\in \operatorname{Fin}(H+1),\quad U_{H}(q)(i)=\begin{cases}q(\langle i.\operatorname{val}+1,h\rangle),& h:i.\operatorname{val}+1<H+1,\\{}0\in \mathbb{R},& \mathrm{otherwise}\end{cases}\\{}\forall q,v\in \operatorname{State}(H), \forall c\in \mathbb{R},\quad U_{H}(q+v)=U_{H}(q)+U_{H}(v),\quad U_{H}(c\cdot q)=c\cdot U_{H}(q)\end{gathered}$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.update` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The update copies coordinate i+1 when that coordinate lies in Fin(H+1), and otherwise writes the real number 0. Both additivity and real scalar compatibility are part of this linear map; Hom over the reals denotes the space of real-linear maps. The boundary value is different from the sign of false. The update uses neither time nor a subsequent input sample.

**Definition 1.7 (A fixed linear readout).**

$$\forall H\in \mathbb{N},\quad R_{H}:=\operatorname{readout}(H)\in \operatorname{Hom}_{\mathbb{R}}(\operatorname{State}(H),\mathbb{R}),\quad \forall q\in \operatorname{State}(H),\quad R_{H}(q)=q(0)$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is the real-linear coordinate-zero projection on the same finite real state.

**Theorem 1.8 (Every in-bound coordinate of every iterate).**

$$\forall H,t\in \mathbb{N}, \forall q\in \operatorname{State}(H), \forall i\in \operatorname{Fin}(H+1), \forall h_{i}:i.\operatorname{val}+t<H+1,\quad \operatorname{update}(H)^{[t]}(q)(i)=q(\langle i.\operatorname{val}+t,h_{i}\rangle)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.update_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all H,t, arbitrary real state q and coordinate i satisfying i.val+t<H+1, the t-fold update at i equals the original q at i.val+t. Induction on t applies the successor equation for function iteration; the in-bound inequality selects the copy branch at the successor step. The statement concerns only in-bound coordinates.

**Theorem 1.9 (Pointwise attainment of the original signal).**

$$\forall H\in \mathbb{N}, \forall x\in X, \forall t\in \mathbb{N}, \forall h_{t}:t\leq H,\quad \operatorname{readout}(H)(\operatorname{update}(H)^{[t]}(\operatorname{initState}(H,x)))=\operatorname{signal}(t,x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.pointwise_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the arbitrary-state invariant to the initialized vector at coordinate zero. For every infinite input x and every t<=H, including H=t=0, the fixed readout after t fixed updates is exactly signal(t,x). This is the finite real construction in original theorem 12.4. In the binary-shift source, the unit-word orbit at coordinate j is x(j+word.length); its coordinate-zero sign observation is therefore this same signal at time t. The construction proves the pointwise upper realization. It asserts no lower bound, minimum dimension, state cardinality, after-boundary identity, or almost-everywhere endpoint.

## References

- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.State`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.X`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.bitSign`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.initState`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.pointwise_attainment`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.readout`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.signal`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.update`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.update_iterate`
