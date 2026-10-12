# Generator Row Stability

## Abstract

A complete generator cycle controls phase after translation, and two complete rows control unequal spectral amplitudes with a source-energy counting bound.

**Theorem 1.1 (Complete cyclic correction from real defect lifts).**

Lean statement: `D5/S3/Fourier/GeneratorRowStability.complete_cycle_phase_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GeneratorRowStability.complete_cycle_phase_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive cyclic order N, let z:ZMod N->Complex have unit norm and z(0)=1. Supply real lifts theta with theta(0)=0 and exp(i theta(k))=z(k)z(1)conj(z(k+1)) for every k, including the final wraparound row. If |theta(k)|<=omega and omega>=0, one actual t:ZMod N satisfies |z(k)-stdAddChar(-(k*t))|<=(N-1)omega/2 at every frequency. The lifts need not be principal and no bound on N*omega is imposed.

Write S=sum_{j=0}^{N-1}theta(j). The full recurrence, evaluated also at N, gives z(k)=z(1)^k exp(-i sum_{j<k}theta(j)) and the root q=z(1)exp(-iS/N) with q^N=1. After centering, the phase is Phi(k)=kS/N-sum_{j<k}theta(j). The zero lift improves the prefix bound to (k-1)omega, so |Phi(k)|<=((N-k)(2k-1)/N)omega. The discrete identity N(N-1)-2(N-k)(2k-1)=(2k-N)(2k-N-1)>=0 proves the desired coefficient; it uses that the two factors are consecutive integers. The global chord<=angle estimate then applies even when accumulated phase is large.

Mathlib AddChar.zmodChar and FinitePoisson.characterEquiv turn q into a cyclic character. Taking the negative inverse character coordinate gives exactly stdAddChar(-(k*t)), with the translation sign used below. The order-one case has zero bound and remains in the theorem telescope.

**Theorem 1.2 (Equal-amplitude counting stability with exact source energy).**

Lean statement: `D5/S3/Fourier/GeneratorRowStability.equal_amplitude_signal_energy_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GeneratorRowStability.equal_amplitude_signal_energy_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f,g be arbitrary complex signals on ZMod N, with the unnormalized negative-exponent spectra F=dft(f), J=dft(g). Assume m>0, 0<=epsilon<=m^3/4, exact complex DC F(0)=J(0), |F(k)|>=m and |J(k)|=|F(k)| at every k. The complete generator-row residual |J(k)J(1)conj(J(k+1))-F(k)F(1)conj(F(k+1))| is at most epsilon for every k, with cyclic addition and wraparound. Define E_F=(1/N)sum_{k!=0}|F(k)|^2 from the actual source. The theorem produces one t with sum_x|g(x)-f(x-t)|^2<=16(N-1)^2 epsilon^2 E_F/(63m^6). No all-pairs row, zero row, upper spectral bound, reality, positivity or uniqueness premise is added.

Equal amplitudes are load-bearing: z=J/F is unit-valued and exact DC gives z(0)=1. The raw residual factors exactly as F(k)F(1)conj(F(k+1)) times (z(k)z(1)conj(z(k+1))-1). Thus each phase chord is bounded by delta=epsilon/(|F(1)|m^2), which is at most epsilon/m^3<=1/4. For a principal angle theta, d=|exp(i theta)-1|=2|sin(theta/2)|. Real.le_tan together with cos(theta/2)^2>=63/64 gives |theta|<=8d/sqrt(63), preserving the half-angle factor 2. Consuming the complete-cycle theorem gives phase error at most 4(N-1)delta/sqrt(63). Its square produces the exact 16/63.

The Fourier residual is (z(k)-stdAddChar(-(k*t)))F(k), and its DC value is exactly zero. The original public FullBispectrumStability.dft_translation identifies the actual signal f(x-t); its cyclic_parseval converts counting squared error to (1/N) times spectral squared error. Removing DC leaves precisely E_F. Internally delta retains |F(1)|^2m^4 in the denominator; |F(1)|>=m supplies the stated m^6 bound. N=1, epsilon=0 and the inclusive epsilon=m^3/4 endpoint are all included. No smallness of N*epsilon is used.

This source-conditioned equal-amplitude estimate also has an unequal-amplitude two-row extension below. The order-nine source-uniform obstruction is compatible with this estimate because source energy is allowed to grow. These are repository-derived proofs with direct Mathlib and repository reuse; no literature novelty claim is made. Model proof plans are not kernel evidence.

**Theorem 1.3 (Unequal-amplitude stability from two complete rows).**

Lean statement: `D5/S3/Fourier/GeneratorRowStability.unequal_amplitude_signal_energy_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GeneratorRowStability.unequal_amplitude_signal_energy_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive cyclic order N and arbitrary complex signals f,g, write F=dft(f), J=dft(g) in the unnormalized negative-exponent convention. Assume m>0, 0<=epsilon<=m^3/4, exact complex F(0)=J(0), and |F(k)|>=m for every k. For every cyclic k, including wrap, both residuals |J(0)J(k)conj(J(k))-F(0)F(k)conj(F(k))| and |J(k)J(1)conj(J(k+1))-F(k)F(1)conj(F(k+1))| are at most epsilon. With the existing sourceEnergy f=(1/N)sum_{k!=0}|F(k)|^2, one actual t:ZMod N satisfies sum_x|g(x)-f(x-t)|^2 <= epsilon^2 sourceEnergy(f)(1+(N-1)^2)/(3m^6). No target spectral floor, equal-amplitude premise, all-pairs observation, accumulated-phase smallness, real-positive signal condition, uniqueness or algorithm is assumed or concluded.

Set a=|F(k)|, b=|J(k)| and aDC=|F(0)|. The complex calibrated zero row gives aDC|b^2-a^2|<=epsilon. Since m^3<=aDC*a^2, comparison of squares gives 3a/4<=b<=5a/4 and b>0. Factoring b^2-a^2 and using b+a>=7a/4 yields (b-a)^2<=16epsilon^2/(49aDC^2*a^2) <=epsilon^2/(3aDC^2*a^2). The source floor then bounds this by epsilon^2*a^2/(3m^6). Target nonvanishing is thus derived from the zero row.

Reuse the original private phase, phase_norm and phase_reconstruct from FullBispectrumStability. The unit relative phase is z=phase(J)conj(phase(F)), with z(0)=1. Each radial generator residual is |P-Qr|<=epsilon, where P=a(k)a(1)a(k+1)>=m^3, Q=b(k)b(1)b(k+1)>0 and r=z(k)z(1)conj(z(k+1)). Put delta=epsilon/m^3<=1/4. The exact squared projection identity |P-Qr|^2=(Q-P Re(r))^2+P^2 Im(r)^2 implies Re(r)>0 and Im(r)^2<=delta^2. For theta=Arg(r), x=|theta|<pi/2, cos(x)=Re(r) and sin(x)^2=Im(r)^2. Real.le_tan gives x*cos(x)<=sin(x); squaring and cos(x)^2>=15/16 give 15theta^2<=16delta^2.

Choose an attained maximum omega=max_k|Arg(r(k))| locally. The original complete_cycle_phase_correction consumes every real lift, with theta(0)=0 and no N*delta restriction, and provides one translation with phase squared distance <=4(N-1)^2delta^2/15. The original WHOLE radial_identity gives |J(k)-chi(k)F(k)|^2=(b-a)^2+ab|z(k)-chi(k)|^2. Its phase term uses b/a<=5/4 and (5/4)*(4/15)=1/3; no triangle bound replaces this identity. Exact DC makes the zero error vanish. Original unit_mul_conj, dft_translation and cyclic_parseval then recover the actual f(x-t) and the counting sum, leaving exactly the non-DC source energy. N=1, epsilon=0 and the inclusive epsilon=m^3/4 endpoint stay in scope.

The source-owned dependent-family registration observes actual g(x) only in the output slot and preserves every original input and antecedent. The lawful N=1,f=g=1,m=1,epsilon=0 instance rejects zero output: the output error is one while the bound is zero. Whole-family variation and sensitivity use actual signal data. The scalar and angle estimates are private, consumed proof content; no additional public framework, forwarding theorem or literature novelty claim is introduced.

## References

- Truth anchor: `D5/S3/Fourier/GeneratorRowStability.complete_cycle_phase_correction`
- Truth anchor: `D5/S3/Fourier/GeneratorRowStability.equal_amplitude_signal_energy_stability`
- Truth anchor: `D5/S3/Fourier/GeneratorRowStability.unequal_amplitude_signal_energy_stability`
- Dependency: [D5/S3/Fourier/FullBispectrumStability](FullBispectrumStability.md)
