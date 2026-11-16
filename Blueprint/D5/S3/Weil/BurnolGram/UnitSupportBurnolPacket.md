# Unit Support and Explicit Peak Radius

## Abstract

The actual packet can be reconstructed with B=K=1; localization support is N+2 and two peak seminorms give a numerical exceptional-radius test.

**Theorem 1.1 (Construct both unit-support components).**

Lean statement: `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.exists_unit_support_orbitBurnolPacket`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.exists_unit_support_orbitBurnolPacket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Retain support from the stronger finite reflection-compatible interpolation theorem at both stages. All signed values, exception annihilation and tail properties are proved using the existing packet construction. No old arbitrary packet is claimed to have these radii.

**Theorem 1.2 (Specified final support radius).**

Lean statement: `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.unit_support_burnol_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.unit_support_burnol_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the existing additive convolution support theorem to B=K=1. The radius is common to all coefficients.

**Theorem 1.3 (Explicit exceptional spectral radius).**

Lean statement: `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.peak_tail_of_two_jet_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.peak_tail_of_two_jet_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the derived two-jet closed-strip decay and the unconditional half-strip bound on gamma. The spectral-radius versus real-ordinate conversion is proved using the complex norm square. The finite target set must also be included when assembling a packet.

Application: the amplitude price of resolving one signed orbit. The following is an elementary application derivation, not an additional kernel-checked declaration or a literature novelty claim. The existing unit-support theorem fixes a window for each finite interpolation problem; it does not bound the interpolant's size uniformly over moving nodes. This application supplies a necessary resource test for that exact construction.

The classical exponential-type difference bound and its Fourier normalization are recorded in `D5/L/Fourier/boas1956inequalities`. The proof below keeps the extra evenness factor and the actual signed packet data explicit.

For every R>0, t real and eta real with t*eta nonzero, take any complex smooth even function g supported in [-R,R]. All following integrals are over the whole real line. Set F(z)=integral exp(-i*z*x)*g(x) dx, z_plus=t+i*eta, z_minus=t-i*eta, L0=integral |g(x)| dx, L2=integral |g''(x)| dx, m=min(1,R*|t|), and S=m*sinh(R*|eta|)>0. Suppose |F(z_plus)-1|<=epsilon and |F(z_minus)+1|<=epsilon, where 0<=epsilon<1. Then L0*S>=1-epsilon and L2*S>=max(0,|t^2-eta^2|-(t^2+eta^2)*epsilon). In particular exact interpolation requires L0>=1/S and L0+L2>=(1+|t^2-eta^2|)/S.

Proof. Compact support makes every displayed integral absolutely convergent. Changing x to -x and using evenness gives F(z)=integral cos(z*x)*g(x) dx. The exact kernel difference is cos((t+i*eta)*x)-cos((t-i*eta)*x)=-2*i*sin(t*x)*sinh(eta*x). On the support, |sin(t*x)|<=min(1,R*|t|) and |sinh(eta*x)|<=sinh(R*|eta|). The integral triangle inequality therefore gives |F(z_plus)-F(z_minus)|<=2*S*L0. The two error disks give the opposite bound 2*(1-epsilon), proving the first inequality. This proof also works for any integrable even g with the same support; smoothness is needed for the next step.

The second derivative is even and has the same support bound. Twice integrating by parts, with zero boundary terms by smooth compact support, gives F_{g''}(z)=-z^2*F(z). Write F(z_plus)=1+e_plus and F(z_minus)=-1+e_minus, with both errors bounded by epsilon. The difference of the two derivative transforms is -z_plus^2-z_minus^2-z_plus^2*e_plus+z_minus^2*e_minus. Its modulus is at least 2*|t^2-eta^2|-2*(t^2+eta^2)*epsilon. Apply the first kernel estimate to g'' and use L2>=0. This proves the second inequality; adding the exact-interpolation inequalities proves the two-jet bound.

This also identifies the two collisions in the existing GautschiEvenInterpolationBounds application: |z_plus^2-z_minus^2|=|z_plus-z_minus|*|z_plus+z_minus|=4*|t*eta|. Its interpolation upper bounds retain both direct and reflected separation. The present lower bound shows that a uniformly bounded signed readout cannot evade those collisions by choosing different interpolation coefficients. When both R*|t| and R*|eta| are small, S is asymptotic to R^2*|t*eta|. This conclusion comes from the actual evaluation functional, not from reversing an upper estimate for a particular Lagrange basis.

The actual-object map is rho=beta+i*t and gamma=(rho-1/2)/i=t+i*(1/2-beta), so eta=1/2-beta. For any supplied finite orbit frame and index j, set g=P.killer(j). The killer_values field of OrbitBurnolPacket gives F(gamma)=1 and F(conjugate(gamma))=-1 at that orbit. For a unit-support packet take R=1 and epsilon=0. Thus its actual zeroth and second L1 seminorms must pay the displayed bounds; any certified upper budgets J0 and J2 must be at least these actual seminorms. At fixed nonzero t and fixed R, the lower bound for L0 is asymptotic to 1/(m*R*|eta|) as eta tends to zero. This is a conditional statement about any such frames, not an assertion that arbitrarily close off-line zeta zeros exist. At eta=0 the two targets contradict each other; at t=0 they also contradict F(z)=F(-z).

A usable budget test follows without an asymptotic approximation. If L0<=L with L>0, then R*|eta|>=arsinh((1-epsilon)/(m*L)), and in particular R*|eta|>=arsinh((1-epsilon)/L). A pointwise amplitude cap |g|<=A gives L0<=2*R*A. For a certified enclosure |eta|<=eta_max, the strict inequality L*sinh(R*eta_max)<1-epsilon rules out the claimed readout within that budget. This is a necessary feasibility test, not a sufficient interpolation criterion. It already allows arbitrarily small positive readout error; exact cancellation is not needed for the obstruction. Explicitly, for every R,L>0 and 0<=epsilon<1, choose t=1/R and eta=arsinh((1-epsilon)/L)/(2*R). Then m=1 and L*sinh(R*eta)<1-epsilon. No even integrable g in that window with L0<=L realizes those two error disks. These are generic spectral nodes, not asserted zeta zeros.

The same test applies to the actual localized basis, not just its seed. In MultiOrbitBurnolUniformRemainder, burnolSynthesis with the one-hot coefficient vector at j still has values +1 and -1 at that orbit. The unit-support theorem supplies the radius cap R_N=N+2. If its final L1 norm is at most a fixed L, necessarily (N+2)*|eta|>=arsinh(1/L). Consequently fixed final amplitude and radius cannot be traded for an arbitrarily small off-line distance by increasing a nominal resonance count alone. If N+1=2^k is evaluated by repeated squaring, the available radius cap is 2^k+1. Logarithmically many multiplication stages can therefore conceal an exponentially growing support budget; this calculation neither disproves such a stage count nor proves a lower bound for arithmetic running time.

Normalization matters. With targets a and -a and absolute error at most e, the same triangle argument gives L0*S>=max(0,|a|-e). Shrinking a can keep an absolute L1 budget bounded, but also shrinks the signal and its admissible absolute error. Scaling an entire test by a multiplies its Weil quadratic value by |a|^2. For a nonzero target and e<|a|, the normalized bound is (L0/|a|)*S>=1-e/|a|. Thus the unit-readout bound controls norm relative to signal, not a signal-to-error ratio alone. It asserts no amplitude lower bound for an arbitrarily rescaled, unnormalized negative witness.

What survives is finite conditional interpolation, the existing coefficient-uniform geometric remainder, and rational depth selection once the actual majorant is bounded. The lower seminorm estimate does not lower-bound the mixed spectral majorant: an upper bound built from large seminorms cannot be inverted to obtain such a lower bound. Nor does sparse synthesis imply sparse Gram matrices or a polynomial bit cost. OPEN: for the same actual packet, supply certified node enclosures, separation and target values, upper two-jet budgets, the full mixed head-tail majorant and a bit-cost bound as functions of height, off-line distance, channel count and tolerance. The feasibility inequality above is an immediate falsifier for any proposed simultaneous budget. A model slider may show this conditional forbidden region, but supplies neither an off-line zero nor an RH certificate.

## References

- Truth anchor: `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.exists_unit_support_orbitBurnolPacket`
- Truth anchor: `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.peak_tail_of_two_jet_budget`
- Truth anchor: `D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.unit_support_burnol_radius`
- Dependency: [D5/S3/Weil/BurnolGram/WeilMixedHeadTailBudget](WeilMixedHeadTailBudget.md)
