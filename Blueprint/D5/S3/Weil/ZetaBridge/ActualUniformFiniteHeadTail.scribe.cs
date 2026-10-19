using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualUniformFiniteHeadTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform coefficient lower tails for the full arithmetic divided-difference column on nonempty finite integer heads.",
        H("Uniform actual finite-head tails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-finite-head-uniform-tail-lower"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower"),
                H("A constant and cutoff uniform in every complex head coefficient vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural c with 2 <= c, every finite set S of integers, and a proof that S is nonempty, there exist a real C > 0 and a natural N0 such that, for every function v from integers to complex numbers and every natural N with N0 <= N, the following two assertions hold. The sequence indexed by natural j with value norm(couplingColumn(c,S,v,Int.ofNat(N+j+1)))^2 + norm(couplingColumn(c,S,v,-Int.ofNat(N+j+1)))^2 is summable. Its actual infinite sum is at least C times the finite sum of norm(v(n))^2 over n in S, divided by ((N : Real)+1)^(2*card(S)-1). C and N0 are quantified before v and N. The zero function, singleton heads, arbitrary complex coefficients, and c=2 are included.")),
                    Paragraph(Text("The actual column is the sum over n in S of the complex cast of (arithmeticBoundarySymbol(c,n)-arithmeticBoundarySymbol(c,m))/(pi*((m : Real)-(n : Real))), multiplied by v(n). The boundary symbol retains the pole term, the entire infinite Gamma series and the finite prime sum. Let d=card(S) and choose A=max(1, the supremum of natAbs(n) over n in S). The nodal polynomials D, P and Q in ActualNodalCoercivity give pi*D(m)*couplingColumn(c,S,v,m)=P(m)-arithmeticBoundarySymbol(c,m)*Q(m) outside S, with both numerator degrees below d. Their uniform reconstruction constant is lambda=1/(d^2*A^(2*(d-1))).")),
                    Paragraph(Text("Dilate P and Q by the positive integer scale N and split their coefficients into even and odd parts Pe, Po, Qe and Qo without reducing their degrees. Put gamma=pi/4, F1=Pe+gamma*Qo, F2=Po+gamma*Qe, B1=Qo and B2=Qe. For positive m, write p(m) for the actual finite prime symbol and delta(m)=m^2*smoothWeight(c,m)-gamma. The exact smooth split gives s(m)=-(gamma+p(m)+delta(m)), and the existing boundary reflection identity gives s(-m)=-s(m). At t=m/N the positive numerator is U1(t)+U2(t), and the negative numerator is U1(t)-U2(t), where Ui=Fi+(p(m)+delta(m))*Bi. The parallelogram identity gives paired numerator energy 2*(norm(U1)^2+norm(U2)^2).")),
                    Paragraph(Text("For E=sum over r<d of N^(2*r)*(norm(P_r)^2+norm(Q_r)^2), the two F channel coefficient energies add to EP+gamma^2*EQ and the two B channel energies add to EQ. Disjoint coefficient parities remove their cross terms. Since 0<gamma<1, gamma^2*E <= EF <= E and EB <= E. No head coefficient, moment or parity condition is imposed.")),
                    Paragraph(Text("The degree-only discrete sampling constant kappa is chosen before N and every polynomial. Let R=sum over r<d of 4^r and H=primeFirstMoment(c). Signed polynomial interference is controlled by Abel summation before taking its absolute value. The Gamma estimate chooses K before m with abs(delta(m))<=K/m. Finite Cauchy-Schwarz on t in [1,2] bounds evaluation energy by R times coefficient energy. For arbitrary real p and delta, retain the complete nonnegative square (p+delta)^2*norm(B)^2 in the exact norm expansion. The sole smooth loss is at most abs(delta)*(norm(F)^2+norm(B)^2), using 2*abs(Re(F*conj(B)))<=norm(F)^2+norm(B)^2. This needs no pointwise bound on p. Summing the smooth error over the exactly N modes N<m<=2*N costs at most K*R*(EF+EB), hence at most 2*K*R*E. Consequently the channel annulus energy is at least (kappa*gamma^2*N-T)*E, where T=R*(4*H+2*K).")),
                    Paragraph(Text("Choose N0 beyond 1, 2*A, 2*d and 2*T/(kappa*gamma^2). The channel annulus then has energy at least kappa*gamma^2*N*E/2. Both signs are outside S; their nonzero nodal denominators have norm at most (3*N)^d. Combining this bound with the exact polynomial model, the factor two from the parallelogram identity and nodal reconstruction gives the positive witness C=kappa*gamma^2*lambda/(pi^2*3^(2*d)). The identity 2*d=(2*d-1)+1 cancels the positive scale factor N, including d=1. Monotonicity replaces N by N+1 in the final denominator.")),
                    Paragraph(Text("ActualFullSymbolTail.paired_coupling_column_tail establishes summability at the internally verified head separation. Reindexing the annulus as j in range(N) and applying Summable.sum_le_tsum compares its nonnegative energy with this genuine infinite tail. The constant and cutoff depend only on the data chosen before the coefficient vector.")),
                    Paragraph(Text("The mathematical ingredients are classical finite Lagrange interpolation and integer node separation, finite Cauchy-Schwarz, the parallelogram identity, discrete polynomial sampling, Abel summation for finite prime phases, and the positive Gamma integral comparison. This is an estimate for the defined arithmetic column. It asserts no physical Weil positivity, Fourier or physical operator identification, Robin inequality, or Riemann hypothesis result."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/ActualNodalCoercivity")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Interpolation/DiscreteCoefficientSampling")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/PrimePolynomialInterference")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/ActualFullSymbolTail"))]));
}
