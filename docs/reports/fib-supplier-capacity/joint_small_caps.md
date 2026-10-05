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

The data are ordinary finite arithmetic evidence for the stated source contract. They do not enumerate all controllers, certify an installed runtime, or establish a physical memory or paid-cost optimum.
