# Actual three-setting qubit recovery

## Abstract

Three actual qubit expectation settings recover a density matrix with a sharp trace-norm noise bound and physical restoration without larger error.

**Theorem 1.1 (Exact reconstruction, sharp noise, and physical projection).**

$$\begin{aligned}0\le p\le1, x^{2}+y^{2}\le p(1-p)\\m_{0}=p, m_{1}=r+hp+2bx, m_{2}=r+hp-2by\\p=m_{0}, x=\frac{m_{1}-r-hm_{0}}{2b}, y=\frac{r+hm_{0}-m_{2}}{2b}\\0\le epsilon, |eta_{0}|\le epsilon,|eta_{1}|\le epsilon,|eta_{2}|\le epsilon\longrightarrow\frac{traceNorm(rhoHat-\rho)}{2}\le\sqrt{1+2phi}epsilon\\0<epsilon\le\frac{1}{2\sqrt{1+2phi}}\longrightarrow\frac{traceNorm(rhoHat-\frac{I}{2})}{2}=\sqrt{1+2phi}epsilon\\PSD(rhoProj), trace(rhoProj)=1, \frac{traceNorm(rhoProj-\rho)}{2}\le\frac{traceNorm(rhoHat-\rho)}{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/ActualThreeSettingRecovery.actual_three_setting_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let phi be the real golden ratio, r=1/phi, s=sqrt(r), b=rs, and h=r squared minus r. The actual complex matrices are P=diag(1,0), Q=[[r squared,b],[b,r]], and V=diag(i,1). For 0<=p<=1 and x squared plus y squared at most p(1-p), rho=[[p,x+iy],[x-iy,1-p]] is positive semidefinite with trace one. P and Q are positive semidefinite projections, and V is unitary.

The three real expectations m0=Re tr(P rho), m1=Re tr(Q rho), and m2=Re tr(Q V rho V adjoint) are the population readouts of the three settings, not individual measurement outcomes. They equal p, r+hp+2bx, and r+hp-2by, respectively. Since b is positive, the displayed inversion recovers all three real state parameters exactly.

For arbitrary real errors eta0, eta1, eta2 with each absolute value at most epsilon, where epsilon is nonnegative, the raw linear estimate has diagonal entries pHat and 1-pHat and upper off-diagonal entry xHat+i yHat. It is Hermitian and trace one; it need not be positive semidefinite. Its error is measured by the actual matrix traceNorm, not by a replacement coordinate norm.

The constant sqrt(1+2phi) is attained simultaneously by eta0=eta1=eta2=epsilon at the physical source rho0=I/2. For every positive epsilon at most 1/(2 sqrt(1+2phi)), all three noisy expectations remain in [0,1], the raw output is positive semidefinite, and its half trace-norm error equals the bound. Thus no smaller uniform constant applies even arbitrarily close to I/2.

Center the raw parameters as (pHat-1/2,xHat,yHat). Multiply this vector by one if its Euclidean radius is at most 1/2, or by (1/2)/radius otherwise, and then restore the first coordinate's center. The resulting matrix is positive semidefinite with trace one. Its actual half trace-norm distance to rho does not exceed the raw distance. These centered coordinates correspond to Bloch coordinates (2x,-2y,2p-1) after scaling and reordering; no Bloch coordinate convention is silently substituted.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/ActualThreeSettingRecovery.actual_three_setting_recovery`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
