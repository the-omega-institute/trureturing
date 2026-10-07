# TM63 small-cap joint control certificate

This report records the finite arithmetic behind TM63 for the complete $h=4$ source domain and caps $H=16,17,18,19$. The retained script is [joint_small_caps.py](joint_small_caps.py); its canonical data are [joint_small_caps.json](joint_small_caps.json).

The enumeration contains 920 unit leaf words with positive four-block compositions and $r+s\le4$, checking all three unit windows. The six supported compositions are $(4,4),(4,8),(4,12),(8,4),(8,8),(12,4)$. Their complete source lift includes every Euler word and every ordered bracketing by the Atomic360/TM47 correspondence.

The four literal initial targets are

| target | representative | initial leaves | leaves after $\rho$ |
| --- | --- | ---: | ---: |
| $(1,(4,4),1,1)$ | $(z,w)=(2,3)$ | 8 | 12 |
| $(1,(8,4),1,1)$ | $(z,w)=(3,4)$ | 12 | 16 |
| $(0,1,12)$ | $(z,w)=(3,5)$ | 12 | 20 |
| $(0,1,16)$ | $(z,w)=(4,5),(4,6),(4,7)$ | 16 | 20 or more |

The two-call consumer first attempts the original $\rho$, then appends the actual right context $a^{H-12}$. Equality is accepted. Its response words are `AA`, `AR`, `RA`, `RR` in the table order for every listed cap and every enumerated source word. Initial `Read` has one value; a single modification call has at most two responses. The code checks the Kraft equality $4\cdot2^{-2}=1$, three reachable REQUEST values, and two worst-case modification and total source calls.

The source-transport check replays three fixed mixed histories on six actual words, one for each supported composition, at all four caps. These histories use left and right positive contexts, accepted and rejected $\rho$, and an exact Read after each of 312 modification attempts. There are 34 equality acceptances and 190 rejections. At every step the directly evaluated actual three-window product agrees with the ordered $P\odot F^j(W_3(t))\odot Q$ invariant. The program uses the existing exact Clifford matrices; $F(x_0,x_1,x_2)=(x_1,x_2,J(x_0))$ and the three-step $J$ are checked against actual leaf replacement. This finite sample corroborates the paper's arbitrary-history induction; it does not enumerate all mixed histories.

Two reachable witnesses specify the limits of the response premises. At $H=16$, the actual unit word `abbabaab` accepts right context `a`, then accepts $\rho$: its sizes are 8, 9, 13 and its two resulting exact Read values are $A,B$. Here $J(A)=A+B$ differs from the single-replacement response $B$. Also at $H=16$, looping on acceptance of right context `ba` and entering one common Read state on rejection yields $S^4,S^2,1$ for initial sizes 8, 12, 16. The accepted repetition counts across all six composition witnesses are 4, 2, 2, 0, 0, 0; the rejected candidate always has 18 leaves. These are three distinct exact Read responses. This loop is a reachability witness, not a successful four-target controller. The paper's binary graph count applies only to modification-only states; its lower bound with Read uses paired actual runs.

The data are ordinary finite arithmetic evidence for the stated source contract. They do not enumerate all controllers, certify an installed runtime, or establish a physical memory or paid-cost optimum.
