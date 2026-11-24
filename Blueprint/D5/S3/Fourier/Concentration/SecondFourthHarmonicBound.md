# A sharp bound from the second and fourth harmonics

## Abstract

Second and fourth harmonic bounds give an attained bound on the first harmonic.

**Theorem 1.1 (The largest first harmonic for two prescribed caps).**

$$\begin{aligned}\forall L \in \mathcal{P}, (\left|m_{2}(L)\right| \leq e \land \left|m_{4}(L)\right| \leq k \implies \left|m_{1}(L)\right| \leq B)\\\exists L \in \mathcal{P}_{3}, (\left|m_{2}(L)\right| \leq e \land \left|m_{4}(L)\right| \leq k \land \left|m_{1}(L)\right| = B)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SecondFourthHarmonicBound.sharp_second_fourth_harmonic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite family of unit phases and one set of nonnegative real weights summing to one. Write P for these laws and P₃ for laws on three indexed phases, allowing zero weights. The moments m₁, m₂, and m₄ are weighted first, second, and fourth powers. The caps e and k lie in [0,1]. Put b=min(e,sqrt((1+k)/2)) and r=(1+b)/2. For b=1 the bound B is one. For b<1 put a=min(sqrt(r),sqrt((1+k)/(4(1−b)))) and B=(a+r)/(1+a). The upper bound is attained with at most three phases.

Rotate the phases so that the first moment is nonnegative real. For the real projections x the second cap and the fourth cap give an upper bound r on the mean of x². In the branch a=sqrt(r), the weighted Cauchy–Schwarz inequality gives B. In the other branch the fourth harmonic bounds the mean of x²−x⁴. The pointwise quartic comparison with remainder (1−x)(x−a)²(x+1+2a) then bounds the mean of x.

For b<1 the attaining law puts weight (r−a²)/(1−a²) at 1 and splits the remaining weight between conjugate unit phases with real part a. For b=1 take a point mass. In particular the bound for e=k=0 is 2/3.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/SecondFourthHarmonicBound.sharp_second_fourth_harmonic_bound`
