# Extending the retained incidence to the full finite accepted cell

The chronology construction in [Overlapping spatial records and retained chronology](RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md) deliberately restricts its exact recovery claim to the three-history cell $H$ of weight-one prefixes. The same source contract has a second positive weight-two cell in $E_1$. This continuation checks that remaining cell and identifies one source-derived incidence that removes its residual boundary collision.

This is an ordinary finite classical construction with no Lean verification. It keeps the original source, parser, seed law, selector, bookmark, suffix, Stop and decoder. It does not claim a general scope theorem, a physical spacetime law, or a global completion.

## 1. The full finite support and the old collision

Keep the parameters of the preceding chronology volume: $m=2$, $d=1$, $\ell=2$, $n=4$, actual seed $\rho=1$, and the zero-return fingerprint cell $E_1$. The six positive accepted marker words are

$$
1100,\qquad 1010,\qquad 0110,\qquad 1001,\qquad 0101,\qquad 0011.
$$

The first three have selected prefixes of weight two; the last three are the weight-one cell $H$. Their selected event words are respectively

$$
bda,\qquad bad,\qquad abd,\qquad bac,\qquad abc,\qquad acb,
$$

where $a$ is the first zero, $c$ the second zero, $b$ the first one and $d$ the second one. The original parser identifies these events from the old fields $(t,\beta)$ and the newly acquired marker $e$:

* $e=0$ and $t-\beta=0$ gives $a$;
* $e=0$ and $t-\beta=1$ gives $c$;
* $e=1$ and $\beta=0$ gives $b$;
* $e=1$ and $\beta=1$ gives $d$.

The old scopes are

$$
S_1=\{a,c\},
\qquad
S_2=\{b,c\}.
$$

On the weight-two cell, all three selected prefixes have the same old records; the first-marker register is shared only by the first two:

$$
Q_{\rm old}=(a,b),
\qquad Z=1\text{ for }110,101,
\qquad Z=0\text{ for }011.
$$

The bare snapshot and the continuing output are also common:

$$
B_2=(\rho,\ell,t,\beta,h)=(1,2,3,2,0),
\qquad Y=0,
\qquad s_{\rm stop}=0.
$$

Consequently $110$ and $101$ reach the unchanged decoder with identical $(B_2,Q_{\rm old},Z,Y,s_{\rm stop})$, but their selected pasts differ. This is a concrete remaining fiber of the full $E_1$ source, outside the previous $H$ restriction.

## 2. One actual incidence closes that fiber

Add the second one-event $d$ to the first scope and keep the second scope unchanged:

$$
S_1^+=\{a,c,d\},
\qquad
S_2^+=\{b,c\}.
$$

The writer is causal. Before seed acquisition both records are empty and $Z=0$. On the full marker tree, meaning all $16$ binary words and their prefixes, a completed marker with old $t<3$ is assigned one of $a,b,c,d$ by the four rules above when one of those ordinal identities applies. The writer appends that event to every declared containing scope only in that case. An unmatched ordinal event, every completed marker with old $t\ge3$, and every seed retry, return cycle, partial parse or other non-marker event holds the relation fields. The writer writes $Z=e$ only when old $t=0$. On old $t=2$, the third-marker record update completes before the original snapshot latch while $Z$ holds the value written at the first marker. After the latch, the records and $Z$ hold while the parser advances to the actual fourth marker and the original source delivers its Stop.

This is the same write-before-latch and hold contract instantiated in the source-coherence continuation. The new fact is only the additional membership $d\in S_1^+$; no new read, acceptance bit, replay port or decoder is introduced.

The resulting finite table is:

| full marker word | selected past | event word | $Q^+=(r_1^+,r_2^+)$ | $Z$ | $B$ | $Y$ | Stop | colex rank |
| --- | --- | --- | --- | ---: | --- | ---: | ---: | ---: |
| $1001$ | $100$ | $bac$ | $(ac,bc)$ | 1 | $B_1$ | 1 | 1 | 0 |
| $0101$ | $010$ | $abc$ | $(ac,bc)$ | 0 | $B_1$ | 1 | 1 | 1 |
| $0011$ | $001$ | $acb$ | $(ac,cb)$ | 0 | $B_1$ | 1 | 1 | 2 |
| $1100$ | $110$ | $bda$ | $(da,b)$ | 1 | $B_2$ | 0 | 0 | 0 |
| $1010$ | $101$ | $bad$ | $(ad,b)$ | 1 | $B_2$ | 0 | 0 | 1 |
| $0110$ | $011$ | $abd$ | $(ad,b)$ | 0 | $B_2$ | 0 | 0 | 2 |

Here $B_1=(1,2,3,1,1)$ is the previous weight-one snapshot. The first three rows are unchanged by the incidence because $d$ occurs only after the bookmarked prefix in that cell.

The adapter to the unchanged colex decoder is defined on these realized addresses by

$$
\begin{aligned}
j((ac,bc),z)&=1-z,\\
j((ac,cb),0)&=2,\\
j((ad,b),z)&=2-z,\\
j((da,b),1)&=0.
\end{aligned}
$$

The decoder remains the original total function on its full nonnegative-integer code domain; these equations only specify the finite realized addresses.

## 3. Finite sufficiency and restricted minimality

The table proves that $(Q^+,Z,B,Y,s_{\rm stop})$ determines the selected past on all six positive accepted histories. Conversely, the first three rows are the old chronology witness and the last three rows are separated as follows:

* $(da,b),Z=1$ identifies $110$;
* $(ad,b),Z=1$ identifies $101$;
* $(ad,b),Z=0$ identifies $011$.

Thus the augmented boundary is injective on the selected target set, and the adapter followed by the unchanged decoder recovers every selected prefix.

The added relation is also minimal in a narrow, explicit sense. Keep the two original scopes and the existing first-marker bit, and allow exactly one new membership of one of the four missing incidences $b\in S_1$, $d\in S_1$, $a\in S_2$, or $d\in S_2$. The old weight-two collision $110/101$ remains under the first, third and fourth choices; adding $d\in S_1$ changes their first records to $da$ and $ad$. Hence among this four-element incidence class, exactly one added membership closes the remaining fiber. This is not a minimum over arbitrary memory encodings or total resources.

Without the new incidence, the same old boundary has a target fiber of size two on the weight-two cell. With $d\in S_1^+$, the largest fiber of $(Q^+,Z)$ on the six selected histories is one. The first local record alphabet grows from the realized values

$$
\varnothing, a, ac
$$

to

$$
\varnothing, a, ac, d, ad, da.
$$

This is a real persistent-record cost. It is not an additional chronology register bit: the existing $Z$ remains binary. Routing logic, event labels, writes, parser state, decoder tables, raw Reads, time and energy remain separate resource coordinates.

## 4. Commuting update and four expressions

Let $p(u)=(t,\beta)$ be the original parser projection and let $Q^+(u),Z(u)$ be the new retained fields. For every reachable completed-marker transition on the finite full marker tree, the source update has the bundled form

$$
\mathsf b^+(u)=\bigl(p(u),Q^+(u),Z(u)\bigr),
\qquad
\mathsf b^+(\delta_eu)=\overline F_e^+(\mathsf b^+(u)),
$$

where $\overline F_e^+$ advances the original parser fields, appends the event selected by $(p(u),e)$ to $S_1^+$ or $S_2^+$ only when $t<3$ and one of $a,b,c,d$ is identified, and writes $Z=e$ only at the first marker. Unmatched ordinal events use the same hold branch as non-marker events. After the third-marker latch it holds $(Q^+,Z)$ and the frozen bare snapshot while the original parser performs the fourth marker and produces Stop.

The four expressions on this finite cell are therefore:

| expression | source-derived object | role in the recovery |
| --- | --- | --- |
| space | $S_1^+,S_2^+$ and their event incidences | supplies the two ordered local records $Q^+$ |
| time | the completed event word in the selected prefix | is recovered by the joint boundary address |
| boundary | the latched $B$, frozen $Q^+$ and actual suffix/Stop interface | is the decoder input |
| memory | the causally held first-marker bit $Z$ | separates the residual $ad,b$ fiber |

The recovery is joint and task-relative. The bare scopes, $Q^+$ alone, $Z$ alone, or $B$ alone are not claimed to recover every selected past. The new incidence and the old memory bit are complementary expressions of the missing cross-scope information: the incidence stores the order involving $a$ and $d$, while $Z$ stores whether $b$ preceded $a$; they are not two copies of the same precedence edge.

## 5. Relation to existing supplies and limits

Boundary Dynamics §§25–27 and 36–40 supply the distinction between joint recovery, dynamic sufficiency, local interface compatibility and global completion. Proposition 102.9 in §102.5 supplies the common source, the six positive accepted words, their finite colex dictionaries and causal prefix fields. Sections 104–108 and 114.1 supply the passive selector, write-before-latch, original suffix/Stop interface and unchanged decoder. The preceding [chronology](RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md) and [source-coherence](RECURSIVE_RELATIONAL_OBSERVATION_SOURCE_COHERENCE_CONTINUATION.md) volumes supply the binary $Z$, the first three rows and the source-transition contract.

The new content is the full-$E_1$ residual collision, the actual $d\in S_1^+$ incidence, the six-row adapter and the restricted four-incidence minimality check. It does not introduce a generic quotient, gluing, holonomy, response-index, or projective-limit theorem.

The claims remain bounded:

1. The exact recovery is restricted to the six positive accepted words of this fixed $E_1$ cell, fixed selector and fixed bookmark.
2. The incidence minimum is only within the four one-membership extensions of the two displayed scopes. It is not a total memory, time, energy, raw-Read or implementation optimum.
3. Seed retries, return cycles, incomplete parsing and noncompletion remain actual source events. Their relation fields hold, but their full histories are not reconstructed.
4. Other seeds, longer words, other selectors, other scope families, metric distance, absolute duration, arbitrary protocols, physical laws and global spacetime completion remain open.
5. The derivation is ordinary finite mathematics. It adds no Lean verification and makes no claim that the source contracts are physical laws.

## 追加锚（本行以下为增补区）
