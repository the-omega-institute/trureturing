using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class XiThetaTransformDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The theta transform and completed zeta.",
        H("The theta transform and completed zeta"),
        Blocks(
            Paragraph(Text("The same actual kernel admits a shifted-ray application that detects a nonzero coordinate on the genuine zeta spectrum. Write Phi=romikPhi=sourceThetaKernel, delta=log(2)/2, and J_r(z)=integral_(t>0) Phi^(r)(delta+t)*cos(z*t). There exists an actual index n in zetaZeroData with J_0(zetaZeroData.gamma(n)) nonzero. The spectral parameter is the original complex gamma(n); neither RH nor reality of gamma(n) is assumed.")),
            Paragraph(Text("All derivative and convergence premises are paid for the complete kernel. For every derivative order r and every a>=0, exp(t/2)*abs(Phi^(r)(a+t)) is integrable on t>0 and tends to zero at infinity. The literal mode has the form exp(x/2)*P_r(y)*exp(-y), y=pi*m^2*exp(2x), with P_0=4y^2-6y and P_(r+1)=(1/2-2y)*P_r+2y*P_r'. Split the full series into m=1 and the existing originalTail(1). The existing arbitrary-order tailJet endpoint bounds pay the latter. The first mode uses the quadratic exponential estimate to obtain exp(x/2)*abs(primalJet(r,1,x))<=C_r*exp(-x) for x>=0. Genuine local termwise differentiation and equality on the open positive ray identify these jets with the actual derivatives; no finite-mode substitute or assumed derivative convergence is used.")),
            Paragraph(Text("In the strip abs(Im(z))<=1/2, the elementary exponential formulas bound both abs(cos(z*t)) and abs(sin(z*t)) by exp(t/2). Apply the half-line fundamental theorem to H_r(t)=Phi^(r+1)(delta+t)*cos(z*t)+z*Phi^(r)(delta+t)*sin(z*t), for r=0 and r=2. The paid derivative, integrability and endpoint conditions give J_2+z^2*J_0=-Phi'(delta) and J_4+z^2*J_2=-Phi'''(delta). Thus z^2*(z^2*J_0+Phi'(delta))=Phi'''(delta)+J_4, including z=0. The right side has the uniform norm bound C=abs(Phi'''(delta))+integral_(t>0) exp(t/2)*abs(Phi''''(delta+t)).")),
            Paragraph(Text("At delta every positive mode has y=2*pi*m^2>6, and P_1(y)=-y*(8y^2-30y+15)<0. True summability transfers this sign to Phi'(delta)<0. Put d=-Phi'(delta)>0. The canonical zeta presentation already has finite spectral-radius balls, so one can choose an actual gamma with norm greater than 1+C/d; its nontrivial-zero certificate also places it in the same strip. If J_0(gamma)=0, the exact identity would imply norm(gamma)^2*d<=C, a contradiction. This is a checked application of the existing theta jets, half-line calculus and canonical zero-data interfaces, with no new mathematical declaration or literature-priority claim. The Gaussian interpretation in Suzuki W360 uses the ordinary transform v_delta=2*cPhi*J_0, cPhi=pi^(1/4)/4. A nonzero spectral coordinate alone does not establish nondegeneracy or positivity of the full signed Weil pairing, the original Gamma form-domain, density, or RH.")),
            Paragraph(Text("The physical Gaussian correspondence can be checked on one and the same centered source. For a=log(2)/2 or a=log(4/3)/2, put g_a(x)=exp(9*a/2)*exp(-exp(2*a)*x), let mu(F) be the ordinary full-line integral of actualSuzukiEvenBProfile(F), and set q=mu(g_a)/mu(g_0), F_a=g_a-q*g_0. The actual denominator is nonzero: its even-B image is cPhi*Phi(abs(r)), with cPhi=pi^(1/4)/4, and the actual theta mass is strictly positive. Direct Gaussian moments place g_a, g_0 and their centered combination in originalPhysicalH6 on x>pi. The existing actual-source linearity then gives mu(F_a)=0.")),
            Paragraph(Text("The actual transform is kept literal throughout this application: actualSuzukiEvenBProfile(F_a)(r)=cPhi*(Phi(a+abs(r))-q*Phi(abs(r))). The all-order translated-jet bounds and the Gaussian profile estimates also pay originalGammaFormDomain(c,F_a) for every real c; the required absolute Fourier-energy integral is integrable for each constant shift. On every actual zeta spectral node the unshifted Phi cosine integral is zero by the all-complex xi identity. The centered half-line cosine coordinate therefore equals cPhi times the shifted coordinate, independently of q. For the smaller a=log(4/3)/2, every positive primal mode has y=pi*m^2*exp(2*a)>4, and P_1(y)=-y*(8*y^2-30*y+15)<0 already on y>=4. Summability of the complete derivative series gives Phi'(a)<0, so the same fourth-jet argument supplies a nonzero actual spectral coordinate at this smaller shift as well.")),
            Paragraph(Text("Finally, both exponential tilts at z and -z are absolutely integrable when abs(Im(z))<=1/2. Evenness and reflection of the negative half-line, with the measure-zero endpoint removed, identify the ordinary full-line integral of actualSuzukiEvenBProfile(F_a)(r)*exp(i*z*r) with twice its half-line cosine integral. Thus each of these two explicit centered physical sources simultaneously satisfies original H6, actual zero mean, every real constant-shift Gamma form-domain, and a genuinely convergent full-line transform that is nonzero at some actual, possibly nonreal, gamma(n). This uses the original nontrivial-zero strip and canonical local finiteness without RH. The smaller shift also admits the following original physical moment estimate.")),
            Paragraph(Text("Keep a=log(4/3)/2 and the same actual charge q=mu(g_a)/mu(g_0), and put B=exp(9*a/2)*exp(-(exp(2*a)-1)*pi). The charge is real and its actual normalized value s=q/B satisfies 3/4<s<1; this interval is discharged, rather than assumed. To identify the lower bound, set I_r=integral_(y>0) (6*pi^(5/4)-(pi+y)^(5/4))*exp(-r*y) and C_r=sum_(n>=1) n^4*exp(-pi*r*(n^2-1))*I_(r*n^2). The original physical mean-moment formula gives 5*mu(g_a)=exp(9*a/2-pi*exp(2*a))*C_(exp(2*a)), hence s=C_(4/3)/C_1. Tangent and quadratic bounds for the fractional power control I_r. The auxiliary full tail T=sum_(n>=2) n^2*exp(-pi*(n^2-1)) is strictly less than 1/127 by geometric domination, and the actual mean tail satisfies C_1<=I_1+6*pi^(5/4)*T; the factor 6*pi^(5/4) is retained. These bounds give s>3/4 while retaining every n^4 factor and the original 1/5 normalization. For the upper bound, the actual positive mean kernel on x>pi sends the strictly positive source B*g_0-g_a to a strictly positive mean, giving s<1. No finite theta truncation or surrogate centering functional is used.")),
            Paragraph(Text("Translate the original physical variable by x=pi+y. Up to a positive constant that cancels in the quotient, the squared norm of this SAME F_a becomes W_s(y)=(exp(-4*y/3)-s*exp(-y))^2. Its exact moments are M_k=integral_(y>0) y^k*W_s(y)=k!*((8/3)^(-k-1)-2*s*(7/3)^(-k-1)+s^2*2^(-k-1)). In particular M_0=(s-6/7)^2/2+3/392>0. Each M_k is nonnegative by its integral representation. Expanding (1+y/pi)^6 and using pi<22/7 bounds its integral below by sum_(k=0)^6 binom(6,k)*(7/22)^k*M_k. Subtracting (19/4)*M_0 gives the rational quadratic (-561141687/907039232)*s^2+(20266236/12400927)*s-12877086436497/14860930777088, which is strictly greater than 1/100 throughout 3/4<=s<=1.")),
            Paragraph(Text("Consequently the original quotient integral_(x>pi) x^6*norm(F_a(x))^2 divided by (pi^6*integral_(x>pi) norm(F_a(x))^2) is strictly greater than 19/4. This is a checked application of the existing actual mean representation, Gaussian moments, theta bounds and spectral interfaces: one explicit source now satisfies this moment lower bound together with original H6, actual mean zero, every real constant-shift Gamma domain and a nonzero convergent transform at an actual zeta spectral node. The estimate concerns the original physical quotient; it does not prove positivity or nondegeneracy of the complete signed Weil pairing, or RH.")),
            Paragraph(Text("The same literal ordinary transform v_F(z)=integral_r actualSuzukiEvenBProfile(F)(r)*exp(i*z*r) also has a paid uniform strip envelope. For F=g_a-q*g_0, every a>=0 and every complex q, the complete translated jets, their first and third endpoint values and their zeroth and fourth weighted integral budgets supply an explicit finite K with norm(v_F(z))<=K/(1+norm(z)^2) on abs(Im(z))<=1/2. The fourth-jet identity gives the high-frequency bound; the direct integral budget covers low frequencies, including z=0. This is an estimate for the actual even-B full-line transform, with its integrability supplied on the entire strip.")),
            Paragraph(Text("The complete actual zero-counting theorem zero_sum_inv_sq, transported through ClassicExplicitFormula.zeroEquiv and multiplicity_eq_zeroMult, gives sum_n m_n/(1+norm(gamma(n))^2)<infinity. It retains the analytic multiplicity of every nontrivial zero. Apply the same strip envelope at gamma(n) and conj(gamma(n)); their norms agree and both lie in the paid strip. Then m_n*norm(v_F(gamma(n))*conj(v_F(conj(gamma(n))))) is at most K^2*m_n/(1+norm(gamma(n))^2)^2 and hence has a summable majorant. Thus the actual signed complex zero series is absolutely convergent, in particular for the very same small-shift centered source above. Local finiteness alone is not used to infer this convergence. The conjugated zero is retained; absolute convergence neither turns the pairing into a sum of squared norms nor proves its sign or its equality with the complete arithmetic Weil form.")),
            Describe.Lean(
                DescribeId.Create("integrable-tilted-gaussian"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.integrable_tilted_gaussian"),
                H("Gaussian integrability under exponential tilts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every real b, exp(-x^2+b*x) is integrable on the real line, by the complex Gaussian integral API."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ray-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.ray_integrable"),
                H("Absolute convergence from the kernel bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("If a continuous real function f satisfies |f(x)| <= sourceThetaKernel(x) for all x >= 0, then f(x)*exp(w*x) is integrable on the positive half-line for every complex w."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ray-tendsto"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.ray_tendsto"),
                H("The endpoint at infinity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("Under the same pointwise domination, f(x)*exp(w*x) tends to zero as x tends to positive infinity, for every complex w."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psi-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.psi_integrable"),
                H("Convergence for the theta tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, psi(x)*exp(w*x) is absolutely integrable on x > 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psifirst-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.psiFirst_integrable"),
                H("Convergence for the first derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, psiFirst(x)*exp(w*x) is absolutely integrable on x > 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-halfline-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.kernel_halfline_integral"),
                H("Two integrations by parts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, the integral over x > 0 of sourceThetaKernel(x)*exp(w*x) equals 1/4 + w*psi(0) + (w^2-1/4)*thetaLaplace(w). All endpoint limits and the integrability of each derivative term are proved from the actual theta tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thetamellin-eq-completed"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_eq_completed"),
                H("The symmetric Mellin integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex s, the literal symmetric theta-tail Mellin integral thetaMellin(s) equals completedRiemannZeta-zero(s). Additive cancellation of the two explicit pole terms in the public reconstruction proves this at s=0 and s=1 as well."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-theta-fourier-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_integrable"),
                H("All-complex Fourier integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex z, sourceThetaKernel(x)*exp(i*z*x) is absolutely integrable on the real line. The Gaussian bound absorbs every complex exponential tilt."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thetamellin-center"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_center"),
                H("The logarithmic substitution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, thetaMellin(1/2+w)=2*(thetaLaplace(w)+thetaLaplace(-w)). The proof uses t=exp(2*x) with the exact factor two and justifies splitting the two convergent half-line integrals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-theta-fourier-eq-xi"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_eq_xi"),
                H("The all-complex transform to xi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("Romik (1.11), with the all-complex convention Xi(z)=xi(1/2+i*z) from (1.3), states this Fourier identity for the all-real Phi of (1.8). The repository identifies Phi with sourceThetaKernel and proves the integral equals xiReading(1/2+i*z) for every complex z using two integrations by parts, reflection, and the symmetric Mellin identity. No division by s*(s-1) occurs, so z=0 and z=plus or minus i/2 are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-theta-coefficient-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_coefficient_zero"),
                H("The constant coefficient is one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("The literal normalized theta coefficient sourceThetaCoefficient 0 equals one. The all-complex Fourier identity at zero identifies the total mass with the real xi value at the center, and positivity of the actual kernel proves this denominator is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-theta-normalized"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_normalized"),
                H("Unconditional normalization and positivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(
                    Paragraph(Text("The real xi value at 1/2 is the integral of sourceThetaKernel and is strictly positive; sourceThetaDensity has integral one; every sourceThetaCoefficient k is strictly positive. The existing normalization theorem is applied with its constant-coefficient premise now proved.")),
                    Paragraph(Text("The Gaussian dominated even-moment series gives the exact all-jet application to this same normalized source. Put p=sourceThetaDensity, m=Re(xiReading(1/2))>0 and C=(sum thetaMajorant)/m. Continuity and |p(x)|<=C exp(-x^2) follow from the literal density and kernel bound. The Fourier identity at zero identifies xiReading(1/2) with the real number m; dividing the all-complex Fourier identity by this unchanged denominator therefore gives the normalized exponential integral.")),
                    Paragraph(Text("The complex cosine is half the sum of the two exponentials. Both normalized exponential integrals at w and -w are absolutely convergent, and the reflection xi(s)=xi(1-s) identifies their values. Thus integral p(x)cos(w*x) dx=xiReading(1/2+i*w)/xiReading(1/2) for every complex w. Taking w=sqrt(z) gives the literal xiSquareSource, globally including zero and branch-cut points. Its kth normalized jet is (-1)^k sourceThetaCoefficient(k). In particular the positive moment coefficients are not the unsigned Taylor coefficients in square coordinates. This source correspondence supplies no individual sourceCoupling sign or Jensen root-reality conclusion."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/CompletedZetaMellinReconstruction"))
        ]));
}
