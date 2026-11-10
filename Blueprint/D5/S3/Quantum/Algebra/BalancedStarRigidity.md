# Balanced-star rigidity with both environment edges

## Abstract

A single zero probe detects every nonzero real residual in the full balanced three-dimensional star, with an explicit finite positive vector reading.

The algebra A is Matrix(Fin 3,Fin 3,Complex), with ordinary multiplication, conjugate transpose and the positive semidefinite order. Set P=diag(1,1,0), c=diag(1,2,0), and t=((0,0,1),(0,0,sqrt(2)),(1,sqrt(2),0)). Thus both environment edges, of weights 1 and sqrt(2), are retained. The probe condition CornerSA(x) means star(x)=x and P*x*P=x. The orientation sigma is either 1 or -1, and rho ranges over all real numbers.

Write J(a,b)=(ab+ba)/2, K(sigma,a,b)=(sigma*i/2)(ab-ba), s(rho)=rho*diag(1,-2,0), and g(sigma,rho)=K(sigma,c,t)+s(rho). At a probe x define h=K(sigma,c,x), r=J(c,x), k=J(c,t), Rplus=x+(h-k), Rminus=x-(h-k), Splus=t+(r+g), Sminus=t-(r+g), and L=-2*J(x,h-k)-2*J(t,r+g). Here Rp and Rm denote Rplus and Rminus, and Sp and Sm denote Splus and Sminus. These are the complete original labels.

PositiveFunctionals(A) denotes all positive complex-linear maps from A to Complex. For such a phi put read(phi,a)=Re(phi(a)) and B(phi,a,b)=read(phi,a*a)*read(phi,b*b)-read(phi,J(a,b)) squared. Selfadjoint readings are real and B is nonnegative for selfadjoint a,b, by complex Cauchy-Schwarz. The quantified family includes the zero functional and every unnormalised mass phi(1). No faithfulness, normalisation or positive-mass premise is imposed.

For the quantitative statement set u=(2sqrt(2)/3,-1/3,0), e=(1/3,2sqrt(2)/3,0), f=(0,0,1), theta(rho)=8rho/3, D(rho)=(2+12rho squared)/9, E(rho)=(2+4rho squared)/9, A(rho)=3sqrt(D(rho)+theta(rho) squared*E(rho)), Lambda(rho)=sqrt(2)(1+64rho squared/9), M(rho)=3(sqrt(3)+3/2+2abs(rho))(1+theta(rho) squared), delta(rho)=Lambda(rho)-A(rho), and epsilon(rho)=delta(rho)/(2M(rho)). In the formulas below these are respectively dd, ee, amp, lam, bigM, delta and epsilon. Define eta(sigma,rho)=i*sigma*e+theta(rho)*f and xi(sigma,rho,q)=u+q*eta(sigma,rho). The positive functional vectorPhi(v) is the actual map a to star(v) dot (a*v).

**Theorem 1.1 (The explicit finite violation at every nonzero residual).**

$$\forall sigma \in \mathbb{R},\; \forall rho \in \mathbb{R},\; \left(sigma = 1 \lor sigma = -1\right) \Rightarrow \left(rho \ne 0 \Rightarrow \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(dot\left(star\left(u\right), u\right) = 1 \land dot\left(star\left(e\right), e\right) = 1\right) \land dot\left(star\left(f\right), f\right) = 1\right) \land dot\left(star\left(u\right), e\right) = 0\right) \land dot\left(star\left(u\right), f\right) = 0\right) \land dot\left(star\left(e\right), f\right) = 0\right) \land 0 < delta\left(rho\right)\right) \land 0 < epsilon\left(rho\right)\right) \land apply\left(vectorPhi\left(xi\left(sigma, rho, epsilon\left(rho\right)\right)\right), 1\right) = ofReal\left(1 + pow\left(epsilon\left(rho\right), 2\right) \cdot \left(1 + pow\left(theta\left(rho\right), 2\right)\right)\right)\right) \land 0 < \frac{pow\left(delta\left(rho\right), 2\right)}{4 \cdot bigM\left(rho\right)}\right) \land \frac{pow\left(delta\left(rho\right), 2\right)}{4 \cdot bigM\left(rho\right)} \le abs\left(read\left(vectorPhi\left(xi\left(sigma, rho, epsilon\left(rho\right)\right)\right), L\left(sigma, rho, 0\right)\right)\right) - sqrt\left(B\left(vectorPhi\left(xi\left(sigma, rho, epsilon\left(rho\right)\right)\right), Rp\left(sigma, 0\right), Sp\left(sigma, rho, 0\right)\right)\right) - sqrt\left(B\left(vectorPhi\left(xi\left(sigma, rho, epsilon\left(rho\right)\right)\right), Rm\left(sigma, 0\right), Sm\left(sigma, rho, 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/BalancedStarRigidity.exact_finite_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same phi=vectorPhi(xi(sigma,rho,epsilon(rho))) occurs in the mass, the L reading and both Gram budgets. The six frame identities assert that u,e,f are orthonormal in the standard complex inner product. The finite displacement epsilon is strictly positive for every nonzero rho, for either orientation.

The proof evaluates the complete matrices at xi(sigma,rho,q), for every real q. The L reading equals -q*Lambda. With b=(9216rho to the fourth+8496rho squared+648)/1296, d=sqrt(2)(24576rho to the fourth+24192rho squared+2916)/1296 and Q=(164096rho to the fourth+69732rho squared+6561)/1296, the two actual Gram budgets are q squared*(b+q*d+q squared*Q) and q squared*(b-q*d+q squared*Q). The sum of their square roots is bounded by q*A+q squared*M for q>=0. This keeps every finite remainder, including all environment contributions.

The scalar identities A squared=4b and Lambda squared-A squared=20rho squared/9+5888rho to the fourth/81 give delta>0 for rho nonzero. The estimate 4Q<=M squared and the nonnegativity of the actual Gram budgets control the two square roots. Substitution of q=delta/(2M) gives precisely the positive gap delta squared/(4M). No limiting response, supplied Gram identity or additional matrix premise is used.

**Theorem 1.2 (The zero-probe budget alone forces rho to vanish).**

$$\forall sigma \in \mathbb{R},\; \forall rho \in \mathbb{R},\; \left(sigma = 1 \lor sigma = -1\right) \Rightarrow \left(\left(\forall phi \in PositiveFunctionals\left(A\right),\; abs\left(read\left(phi, L\left(sigma, rho, 0\right)\right)\right) \le sqrt\left(B\left(phi, Rp\left(sigma, 0\right), Sp\left(sigma, rho, 0\right)\right)\right) + sqrt\left(B\left(phi, Rm\left(sigma, 0\right), Sm\left(sigma, rho, 0\right)\right)\right)\right) \Rightarrow rho = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/BalancedStarRigidity.zero_probe_forces_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If rho were nonzero, the explicit positive vector functional in the preceding theorem would violate the assumed zero-probe budget by a strictly positive amount. This implication has no P2 premise.

**Theorem 1.3 (All probes and the single zero probe have exactly the same rigidity).**

$$\forall sigma \in \mathbb{R},\; \forall rho \in \mathbb{R},\; \left(sigma = 1 \lor sigma = -1\right) \Rightarrow \left(\left(rho = 0 \Leftrightarrow \left(\left(\forall phi \in PositiveFunctionals\left(A\right),\; pow\left(read\left(phi, g\left(sigma, rho\right)\right), 2\right) \le B\left(phi, c, t\right)\right) \land \left(\forall x \in A,\; CornerSA\left(x\right) \Rightarrow \left(\forall phi \in PositiveFunctionals\left(A\right),\; abs\left(read\left(phi, L\left(sigma, rho, x\right)\right)\right) \le sqrt\left(B\left(phi, Rp\left(sigma, x\right), Sp\left(sigma, rho, x\right)\right)\right) + sqrt\left(B\left(phi, Rm\left(sigma, x\right), Sm\left(sigma, rho, x\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\left(\forall phi \in PositiveFunctionals\left(A\right),\; pow\left(read\left(phi, g\left(sigma, rho\right)\right), 2\right) \le B\left(phi, c, t\right)\right) \land \left(\forall x \in A,\; CornerSA\left(x\right) \Rightarrow \left(\forall phi \in PositiveFunctionals\left(A\right),\; abs\left(read\left(phi, L\left(sigma, rho, x\right)\right)\right) \le sqrt\left(B\left(phi, Rp\left(sigma, x\right), Sp\left(sigma, rho, x\right)\right)\right) + sqrt\left(B\left(phi, Rm\left(sigma, x\right), Sm\left(sigma, rho, x\right)\right)\right)\right)\right)\right) \Leftrightarrow \left(\forall phi \in PositiveFunctionals\left(A\right),\; abs\left(read\left(phi, L\left(sigma, rho, 0\right)\right)\right) \le sqrt\left(B\left(phi, Rp\left(sigma, 0\right), Sp\left(sigma, rho, 0\right)\right)\right) + sqrt\left(B\left(phi, Rm\left(sigma, 0\right), Sm\left(sigma, rho, 0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/BalancedStarRigidity.full_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At rho=0, complex Cauchy-Schwarz gives read(phi,K(sigma,a,b)) squared<=B(phi,a,b) for every positive complex-linear phi and selfadjoint a,b. The standard multiplication identity gives K(sigma,Rplus,Splus)-K(sigma,Rminus,Sminus)=L. Applying the same phi, the triangle inequality and the two square-root bounds yields PB at every selfadjoint PAP probe. The fixed pair c,t also gives P2. All degeneracies and zero mass are included.

This is a statement about the displayed fixed output in the given matrix algebra. It constructs no unknown total response, physical preparation, event menu or physical dynamics. The separate assertion that P2 alone admits rho=1/2 is not included. General inputs, infinite spectra, uniform approximation rates and full original physical-source reconstruction require their separate hypotheses and conclusions.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/BalancedStarRigidity.exact_finite_witness`
- Truth anchor: `D5/S3/Quantum/Algebra/BalancedStarRigidity.full_equivalence`
- Truth anchor: `D5/S3/Quantum/Algebra/BalancedStarRigidity.zero_probe_forces_zero`
