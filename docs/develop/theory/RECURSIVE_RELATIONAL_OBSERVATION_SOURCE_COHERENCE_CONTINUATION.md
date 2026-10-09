# Source-coherent continuation of overlapping records

This continuation closes one finite interface obligation left explicit in [Overlapping spatial records and retained chronology](RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md). The preceding construction shows that the two local records $q$ merge the accepted histories $abc$ and $bac$, and that a causally acquired register $z$ restores the selected-past decoder. Its remaining same-source event contract can be checked on the finite accepted cell below.

The result is an ordinary finite classical calculation. It is source-specific and has no Lean verification. It does not claim a general parser theorem, a global spacetime completion, or a physical time law.

## 1. The finite source cell and the projected event interface

Keep the source, seed, parser, selector, bookmark, suffix and Stop contract of the chronology volume. On the positive cell $H$ there are three selected prefixes

$$
010,\qquad 100,\qquad 001,
$$

with selected chronological event words

$$
abc,\qquad bac,\qquad acb.
$$

Let $u$ denote an actual completed-marker prefix, and let $\delta_e(u)$ denote the same source execution after its next completed marker $e\in\{0,1\}$ has been acquired. A raw event that is not a completed marker is written $\delta_\mathtt{hold}$. It includes the seed prelude, paid retries, return cycles, partial parsing, and post-bookmark suffix events whenever those events do not complete a marker. This is a projection of the original event stream, not a replacement parser.

For a prefix with completed-marker count $t$ and integer marker weight $\beta$, write the already supplied parser fields as $p(u)=(t,\beta)$. The event identity supplied by the original parser is:

* $e=0$ with old $t-\beta=0$ is the first zero event $a$;
* $e=1$ with old $\beta=0$ is the first one event $b$;
* $e=0$ with old $t-\beta=1$ is the second zero event $c$.

Only these three identities are needed on the selected cell. The local scopes remain

$$
S_1=\{a,c\},
\qquad
S_2=\{b,c\},
$$

and $Q(u)$ is the pair of ordered records obtained by appending the completed event to every scope containing it. The chronology register is $Z(u)\in\{0,1\}$, initialized at $0$ and written with the first completed marker; later events hold it.

Define the boundary update maps on the realized states by

$$
\begin{aligned}
U_\mathtt{hold}(p,q)&=q,
&V_\mathtt{hold}(p,z)&=z,\\
U_e(p,q)&=\text{append the event identified by }p\text{ and }e\text{ to its scopes},
&V_e(p,z)&=
\begin{cases}
e,&t=0,\\
z,&t>0.
\end{cases}
\end{aligned}
$$

The variables $t$ and $\beta$ in $U_e,V_e$ are the old fields in $p(u)$, not independently supplied decoder inputs. The source projection used for dynamic closure is therefore

$$
\mathsf b(u)=\bigl(p(u),Q(u),Z(u)\bigr).
$$

The parser fields are already part of the original source interface; the newly retained relation is still only the pair $(Q,Z)$.

Write $\tau_e(p)$ for the original parser's update of the completed-marker fields. The bundled boundary maps used below are therefore

$$
\overline F_e(p,q,z)=\bigl(\tau_e(p),U_e(p,q),V_e(p,z)\bigr),
\qquad
\overline F_\mathtt{hold}(p,q,z)=(p,q,z).
$$

## 2. The finite commuting calculation

The following table evaluates the actual source transitions needed for the three accepted prefixes. `unset` means that the third-marker bookmark has not yet latched.

| old prefix $u$ | old $p(u)$ | event | new prefix | $Q(\delta_e u)$ | $Z(\delta_e u)$ | bookmark |
| --- | --- | --- | --- | --- | ---: | --- |
| $\varepsilon$ | $(0,0)$ | $0$ | $0$ | $(a,\varnothing)$ | $0$ | unset |
| $\varepsilon$ | $(0,0)$ | $1$ | $1$ | $(\varnothing,b)$ | $1$ | unset |
| $0$ | $(1,0)$ | $1$ | $01$ | $(a,b)$ | $0$ | unset |
| $1$ | $(1,1)$ | $0$ | $10$ | $(a,b)$ | $1$ | unset |
| $0$ | $(1,0)$ | $0$ | $00$ | $(ac,c)$ | $0$ | unset |
| $01$ | $(2,1)$ | $0$ | $010$ | $(ac,bc)$ | $0$ | $B_0$ |
| $10$ | $(2,1)$ | $0$ | $100$ | $(ac,bc)$ | $1$ | $B_0$ |
| $00$ | $(2,0)$ | $1$ | $001$ | $(ac,cb)$ | $0$ | $B_0$ |

Here

$$
B_0=(\rho,\ell,t,\beta,h)=(1,2,3,1,1),
$$

as in the preceding volume. The first five rows are the pre-bookmark source states. In the last three rows, the third completed marker has already updated the local records and $Z$ before the bookmark latches $B_0$.

For every row in the table, direct substitution gives the bundled commuting identity

$$
\mathsf b(\delta_e u)=\overline F_e(\mathsf b(u)),
$$

whose $Q$ and $Z$ components are the two identities

$$
Q(\delta_e u)=U_e(p(u),Q(u)),
\qquad
Z(\delta_e u)=V_e(p(u),Z(u)).
$$

For a hold event the bundled identity is $\mathsf b(\delta_\mathtt{hold}u)=\overline F_\mathtt{hold}(\mathsf b(u))$; its new relation components read

$$
Q(\delta_\mathtt{hold}u)=Q(u),
\qquad
Z(\delta_\mathtt{hold}u)=Z(u).
$$

Thus the relevant part of the source run factors through the parser-augmented boundary state $\mathsf b=(p,Q,Z)$:

```text
actual source prefix u  -- delta_e -->  actual source prefix delta_e(u)
          | (p,Q,Z)                                 | (p,Q,Z)
          v                                         v
boundary state         -- Fbar_e -->                boundary state
```

The diagram is asserted only for the displayed completed-marker transitions and for the declared hold class. It does not identify distinct raw events inside that class or claim that their histories can be recovered from $(p,Q,Z)$.

## 3. Snapshot latch and post-bookmark holding

Let $L(u)$ be the snapshot latch, with value `unset` before the third completed marker and value $B_0$ after it. The source contract is a write-before-latch transaction: the third marker first applies $U_e$ and $V_e$, then latches the resulting bare fields as $B_0$. Consequently the augmented snapshot

$$
\widehat B(u)=\bigl(B_0,Q(u),Z(u)\bigr)
$$

is obtained from one actual prefix, rather than by combining a record from one history with a snapshot from another.

After the latch, every hold event and every later completed marker in the accepted cell leaves the retained boundary values $Q$, $Z$ and $B_0$ unchanged. The parser projection still advances: the fourth marker $1$ sends $p=(3,1)$ to $p=(4,2)$, while its $Q$ and $Z$ components are held. The source nevertheless continues its original payload and produces the actual common suffix and Stop values

$$
Y=1,
\qquad
s_{\rm stop}=1,
$$

on all three histories in $H$. The suffix and Stop are outputs of the continuing source; they are not read ahead to choose $Z$ or the bookmark.

The same-source condition is therefore no longer an uninstantiated phrase for this cell: every retained field is produced by the displayed source transition, the latch occurs after the third update, the fourth parser transition is explicit, and the post-latch relation fields are held along the continuing execution. Seed retries, return cycles and incomplete parsing remain real source events, but their projected effect on this boundary is the explicit hold map above. The write-before-latch and post-latch retention are realizations of the source contract already stated in the chronology volume and Boundary Dynamics §114.1, not new global parser axioms.

## 4. Consequence for the selected-past decoder

At the bookmark, the three source histories have the following jointly acquired states:

| selected prefix | chronological word $\omega$ | $(Q,Z)$ | selected-past colex rank |
| --- | --- | --- | ---: |
| $010$ | $abc$ | $((ac,bc),0)$ | $1$ |
| $100$ | $bac$ | $((ac,bc),1)$ | $0$ |
| $001$ | $acb$ | $((ac,cb),0)$ | $2$ |

The adapter from the preceding volume,

$$
j(ac,bc,z)=1-z,
\qquad
j(ac,cb,0)=2,
$$

therefore receives the value produced by the same source run that produced $Q$ and $B_0$. The unchanged decoder returns the corresponding selected past. No independently chosen chronology bit, replay port, or post hoc source selection is being smuggled into the interface.

This proves the finite source-coherence statement:

$$
\boxed{
\text{on }H,
\quad
(Q,Z,B_0,Y,s_{\rm stop})
\text{ is a function of one actual source history and is sufficient for the supplied decoder.}
}
$$

It also preserves the earlier negative result: $Q$ alone still merges $abc$ and $bac$, even though their $B_0$, suffix and Stop agree.

## 5. Four expressions in the coherent finite cell

The four expressions now arise from one executable relation history:

| expression | source-derived object | finite recovery statement |
| --- | --- | --- |
| space | labelled scopes $S_1,S_2$ and shared event $c$ | $Q$ is the pair of scope restrictions |
| time | completed-marker transition sequence $\delta_{e_1}\delta_{e_2}\delta_{e_3}$ | $\omega$ is the selected event order |
| boundary | latched $B_0$ together with the frozen records $Q$ | it is the interface delivered at the bookmark |
| memory | persistent register $Z$ | it retains the missing relation $b\prec a$ |

On $\Omega=\{abc,bac,acb\}$, the maps

$$
\omega\longmapsto(Q(\omega),Z(\omega),B_0)
$$

and the table above give inverse maps. Hence the augmented boundary and the chronological selected word mutually recover on this finite cell. The recovery is joint: the scopes alone, $Q$ alone, $Z$ alone, or the bare snapshot alone do not have the same property.

The new content is the commuting source-to-boundary calculation and the write-before-latch/hold proof. It does not add another generic quotient, gluing, or holonomy theorem; those remain the general supplies in Boundary Dynamics §§25–27, 36–40. The actual parser, source law, positive cell, selector and decoder are supplied by Boundary Dynamics §§97, 100–108 and 114.1, while the overlap and adapter are supplied by the chronology volume.

## 6. Limits and remaining obligations

1. The calculation is restricted to the fixed finite cell $H$ and the three selected histories $\Omega$. It does not prove the same commuting identities for every source cell, seed, scope family or selector.
2. `hold` is a projected event class. The result records what these events do to the retained boundary fields; it does not reconstruct their internal order, retry count, hidden depth or return-cycle history.
3. The mutual recovery is for the supplied selected-past consumer. It does not establish total-memory optimality, arbitrary-protocol recovery, metric distance, absolute duration or a global completion.
4. All claims here are ordinary mathematical derivations from the stated finite source contract. No Lean theorem, physical law or unrestricted implementation claim is asserted.

## 追加锚（本行以下为增补区）
