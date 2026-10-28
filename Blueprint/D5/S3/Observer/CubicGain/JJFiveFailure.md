# The second-J five-level obstruction

## Abstract

The prescribed 64 complete targets realize one simultaneous JJ history tree and defeat five further readings on its unrestricted whole fiber.

The domain is exactly Definition 1.1 of SelfCalibrating Relation Mathematics V: every strictly entrywise positive real 2 by 2 source P with determinant zero and trace one, every nonzero entire real polynomial g of degree at most three, and every real constant drift. The native World 3 representation is bidirectionally equivalent to this domain by CompleteFailure.whole_domain. Lower degrees, either gain sign, sampled or repeated roots, asymmetric sources and all drifts remain in the ambient fiber. No witness choice restricts the decoder's domain.

False means M=[[0,1],[1,1]], true means J=[[0,1],[1,0]]. Words are chronological. The empty acquisition is I, and appending E left-multiplies by E. Every atom is immediately read on the same complete world at its original clock; there are no resets, copies, skipped reads or additional ports. For a suffix u of length five write w=JJ++u, A(w)=acquisition(w), and W(w,e)=world(u,e). The 32 terminal words and their two Boolean slots give 64 labels, even when complete worlds repeat across different words.

$H^{JJ}= (0, J, 24, J, \frac{192}{5})$

For each word beginning JJJ the source map qSource uses the following two unit-J-signature lines. All parameters satisfy absolute value less than one half. These are positive rank-one trace-one sources, and their J trace is one. The equal-column and equal-row lines meet only at Pstar.

$Pstar= \frac{1}{2}\begin{pmatrix}1&1\\1&1\end{pmatrix}, Rzero= \begin{pmatrix}-1&-1\\1&1\end{pmatrix}, Lzero= \begin{pmatrix}-1&1\\-1&1\end{pmatrix}$

$alpha_{w}= \operatorname{tr}(\operatorname{A}(w)Rzero), beta_{w}= \operatorname{tr}(\operatorname{A}(w)Lzero), c_{w}= 4(1+\lvert alpha_{w}\rvert+\lvert beta_{w}\rvert)$

The ordered pair (Q(w,0),Q(w,1)) is fixed by these exact exhaustive cases, with the alpha-zero case taking precedence:

$(Q_{w,0}, Q_{w,1})= (Pstar-\frac{1}{4}Rzero, Pstar+\frac{1}{4}Rzero)\quad alpha_{w}=0$

$(Q_{w,0}, Q_{w,1})= (Pstar-\frac{1}{4}Lzero, Pstar+\frac{1}{4}Lzero)\quad alpha_{w}\neq 0,beta_{w}=0$

$(Q_{w,0}, Q_{w,1})= (Pstar+\frac{beta_{w}}{c_{w}}Rzero, Pstar+\frac{alpha_{w}}{c_{w}}Lzero)\quad alpha_{w}beta_{w}\neq 0$

The last parameters are nonzero and have absolute value less than one quarter. In the first two cases opposite nonzero parameters give different sources. Trace linearity gives tr(A(w)Q(w,0))=tr(A(w)Q(w,1)): in the last case both increments from tr(A(w)Pstar) equal alpha(w)beta(w)/c(w), and in the first two cases both increments vanish.

$P_{A,0}= \frac{1}{768}\begin{pmatrix}607&372+\sqrt{40657}\\372-\sqrt{40657}&161\end{pmatrix}, P_{A,1}= P_{A,0}^{T}$

$P_{B,0}= \begin{pmatrix}\frac{9}{10}&\frac{44+\sqrt{1207}}{90}\\\frac{44-\sqrt{1207}}{90}&\frac{1}{10}\end{pmatrix}, P_{B,1}= P_{B,0}^{T}$

The A determinant identity is 372 squared minus 40657 = 97727 = 607 times 161, and 607+161=768. The B identity is 44 squared minus 1207 = 729, with 729/90 squared=9/100. Both square roots are positive and smaller than their off-diagonal centers. Thus both transpose pairs consist of distinct legal sources. These are the exact prescribed matrices, without symmetry assumptions.

$\operatorname{hC}(t)= \frac{2}{5}(t-4)(t-5)(t-6), dC=48; \operatorname{hA}(t)= \frac{32}{125}(t-5)(t-6)(t-7), dA=\frac{1344}{25}; \operatorname{hB}(t)= \frac{3}{10}(t-4)(t-6)(t-7), dB=\frac{252}{5}$

Each displayed gain is the same entire nonzero cubic throughout its world. All seven-action words beginning JJ are assigned simultaneously: JJJ uses (Q(w,e),hC,dC); JJMM uses (PA(e),hA,dA); JJMJ uses (PB(e),hB,dB). The three cases exhaust the labels and contain respectively 32,16,16 slots. The pair at every word has different sources. Sources and coefficients are fixed by world before any response is specified.

The polynomial coefficients, ordered from constant to cubic, are (-48,148/5,-6,2/5), (-1344/25,3424/125,-576/125,32/125), and (-252/5,141/5,-51/10,3/10). The following three vectors list every sample at clocks 0,1,2,3,4,5,6,7 of those entire gains:

$\operatorname{samplesC}()= (-48, -24, \frac{-48}{5}, \frac{-12}{5}, 0, 0, 0, \frac{12}{5})$

$\operatorname{samplesA}()= (\frac{-1344}{25}, \frac{-768}{25}, \frac{-384}{25}, \frac{-768}{125}, \frac{-192}{125}, 0, 0, 0)$

$\operatorname{samplesB}()= (\frac{-252}{5}, -27, -12, \frac{-18}{5}, 0, \frac{3}{5}, 0, 0)$

Every source has trace one. Its J trace is respectively 1,31/32,44/45 in the C,A,B cases. Since the first JJ has cumulative matrices J,I, all 64 targets have readings (0,24,192/5) at clocks 0,1,2. At JJJ the next reading is 228/5; every descendant clock four, five and six reads 48. The terminal pair agrees at clock seven by the terminal trace equality.

For the A and B arms tr(MPA)=31/32+161/768=905/768 and tr(MPB)=44/45+1/10=97/90. The actual third-M responses coincide: 1344/25-(768/125)(905/768)=1163/25=252/5-(18/5)(97/90). This joins both fourth-action arms at the same entire JJM history. At JJMM, M squared=I+M has A trace 1673/768, giving 1344/25-(192/125)(1673/768)=25207/500. All subsequent A samples vanish.

At JJMJ the clock-four matrix is JM and the B gain vanishes. Fifth J gives J(JM)=M with trace 97/90; fifth M gives MJM=[[0,1],[1,2]] with trace 44/45+2/10=53/45. The responses are 252/5+(3/5)(97/90)=7657/150 and 252/5+(3/5)(53/45)=3833/75. The last two B gain samples vanish. Zero-gain positions still execute and immediately read each chosen atom.

The single shared-ancestor response table is: clock 3 JJJ:228/5; clocks 4,5,6 below JJJ:48; clock 7 w below JJJ:48+(12/5)tr(A(w)Q(w,0)); clock 3 JJM:1163/25; clock 4 JJMM:25207/500; clocks 5,6,7 below JJMM:1344/25; clock 4 JJMJ:252/5; clock 5 JJMJJ:7657/150; clock 5 JJMJM:3833/75; clocks 6,7 below JJMJ:252/5. Together with clocks 0,1,2 this defines the common full response Z(v). The public response function uses suffixes below JJ; fullResponse additionally gives the initial 0 and first-J 24.

**Theorem 1.1 (One labelled assignment, finite failure and whole-fiber failure).**

$$\lvert D\rvert=64\land \lvert U\rvert=32\land \lvert DC\rvert=32\land \lvert DA\rvert=16\land \lvert DB\rvert=16\land K=\operatorname{image}(W,D)\land \operatorname{OriginalDomainCorrespondence}(3)\land (\forall u\in U, \operatorname{W}(u,0)\neq \operatorname{W}(u,1)\land (\forall e\in \{0,1\}, \operatorname{natDegree}(\operatorname{gain}(\operatorname{W}(u,e)))=3)\land (\forall e\in \{0,1\},i\in \{0,1,2,3,4,5,6,7\}, \operatorname{readAt}(\operatorname{W}(u,e),JJ++u,i)= \operatorname{Z}(\operatorname{take}(JJ++u,i))))\land K\subseteq \operatorname{wholeSet}(JJ,H^{JJ})\land \operatorname{FiniteLosing}(5,K,JJ)\land \operatorname{L}(5,\operatorname{wholeSet}(JJ,H^{JJ}),JJ)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/JJFiveFailure.jj_five_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is the finite set of all Boolean lists of length five, D=U times {0,1} is labels, DC consists of labels with first letter J, DA of first two letters MM, and DB of first two letters MJ. W(u,e) is world(u,e), and K is family, the image of D under W. The quantified domain equivalence is the complete unrestricted source/gain/drift equivalence displayed in CompleteFailure.whole_domain at d=3. Z is exactly the preceding complete response table, including original clocks zero through seven. Thus every shared ancestor is checked on the same fixed complete worlds.

For a suffix-prefix v and n with length(v)+n=5, support(v,n) is the union of both slots over every n-letter descendant. Its distinct-pair guard follows from a descendant pair. For either atomic action E, support(v++[E],n) lies in support(v,n+1) and has next response response(v++[E]) on the actual clock length(JJ++v)+1. Backward induction and same-word inclusion give the losing recursion with both actions. Taking v empty gives finite L5 at JJ, and inclusion in the whole unrestricted history fiber gives whole-fiber L5. The nontriviality guard is retained at every node.

**Theorem 1.2 (No complete-target recovery in five further readings).**

$$\neg (\exists P\in \operatorname{Policy}(3), \forall W\in \operatorname{wholeSet}(JJ,H^{JJ}), \operatorname{Identifies}(P,5,JJ,W))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/JJFiveFailure.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed claim is that some arbitrary deterministic Policy 3 identifies every world in the whole compatible JJ fiber within five further original-clock readings. Its result is the literal negation of that claim. A policy may choose either atom or return a complete world at any node. CompleteFailure.loses_excludes_policy applies to the actual whole-fiber L5, so all early stopping decisions are included. This result does not assert original-root impossibility, the affine action consequence of 25.2, a result on the other 192 terminal slots, or a nine-read upper bound.

The construction is the repository-derived joint realization of SelfCalV Theorem 25.1. It consumes the existing native chronological products, source chart and finite failure recursion; the supplied mathematical domain is unchanged. Affine response transport of Lemma 9.2 is context for 25.2 and is not needed to prove this fixed normalized JJ assertion. The inclusion argument is the unrestricted same-history principle of Lemma 9.3. No external identifiability, automaton or width theorem is invoked, and no novelty claim is made.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/JJFiveFailure.jj_five_failure`
- Truth anchor: `D5/S3/Observer/CubicGain/JJFiveFailure.result`
- Dependency: [D5/S3/Observer/CubicGain/CompleteFailure](CompleteFailure.md)
