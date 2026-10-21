using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedCollisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite charged Taylor coefficients on the actual half-Fock tensor module.",
        H("Charged Taylor Coefficients and Finite Correction"),
        Blocks(
            Paragraph(Text("Let D:LatticeData, hu:IsUnit D.G.det and sigma,tau:Charge D. "
                + "The source is Carrier D and the target is ActualTensor D hu. They are distinct modules. "
                + "All charges, including zero, every N:Nat, every signed exponent e:Int and every "
                + "actual tensor input are included. No positivity, homogeneity, eigenstate, locality, "
                + "product, iterate or Jacobi premise is imposed.")),
            Paragraph(Text("Write B=bilinear D sigma tau and Q(q)=chargeNorm D q. Put h=w/v^2 "
                + "and u=v*sqrt(1+h). The scalar Taylor factor is (1+h)^(a/2) times "
                + "((sqrt(1+h)+1)/2)^(-2*B). The input polynomial is translated simultaneously "
                + "in the sigma and tau directions by the actual pairTranslation constructor. "
                + "Each translated monomial has two natural translation degrees d(0),d(1). "
                + "For total=e+Q(sigma+tau)+2*N+d(0)+d(1), its creator contribution is zero "
                + "when total<0, and otherwise is the finite sum over 0<=m<=total of "
                + "collisionScalar(m-d(0)-Q(sigma),B,N) times halfCreationCoeff(sigma,m) "
                + "times halfCreationCoeff(tau,total-m). These are formal coefficients; "
                + "no analytic substitution or convergence claim is used.")),
            Describe.Lean(
                DescribeId.Create("charged-collision-unit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.collisionUnit"),
                H("The normalized square-root unit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("collisionUnit is the unit of PowerSeries Complex whose value "
                    + "is one half times (binomialSeries(1/2)+1). Its constant coefficient is one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.collisionScalar"),
                H("Every scalar Taylor coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a,B:Int and N:Nat, collisionScalar a B N is coefficient N "
                    + "of binomialSeries(a/2) multiplied by collisionUnit^(-2*B). The signed integer "
                    + "power is taken in the power-series unit group."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-oscillator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.collisionOscillator"),
                H("The finite oscillator coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For D:LatticeData, sigma,tau:Charge D, N:Nat and e:Int, "
                    + "collisionOscillator D sigma tau N e is a Complex-linear endomorphism of "
                    + "Oscillator D. It first applies the actual pairTranslation and then evaluates "
                    + "each translated monomial by the finite creator sum described above. "
                    + "Polynomial coefficients and repeated-variable multiplicities are retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-tensor-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.collisionCoefficient"),
                H("The complete actual tensor coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For D:LatticeData, hu:IsUnit D.G.det, sigma,tau:Charge D, "
                    + "N:Nat and e:Int, collisionCoefficient D hu sigma tau N e is chargeScalar "
                    + "D (sigma+tau) times TensorProduct.map of collisionOscillator D sigma tau N e "
                    + "and the chosen groundAction D hu (sigma+tau). Thus it acts on arbitrary "
                    + "oscillator and ground inputs and extends linearly to every ActualTensor D hu."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.collisionField"),
                H("The pointwise lower-truncated collision field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For D:LatticeData, hu:IsUnit D.G.det, sigma,tau:Charge D "
                    + "and N:Nat, collisionField D hu sigma tau N is the NativeField with signed "
                    + "coefficient collisionCoefficient D hu sigma tau N. Its lower bound depends "
                    + "on the actual input. For p tensor g one bound is -Q(sigma+tau)-2*N minus "
                    + "the largest d(0)+d(1) in the support of pairTranslation(p); tensor induction "
                    + "extends this bound to arbitrary inputs. Endomorphism support is not assumed finite."))),
                DescribeRole.Definition),
            Paragraph(Text("The coefficient comparison uses two independently derived recurrences. "
                + "Let C_N(e)x=collisionCoefficient D hu sigma tau N e x, let J_tau be the "
                + "tau-weighted sum of singletonLinear current insertions and let "
                + "r_j=halfBinomial(j)/(j+1). Then (N+1)*C_(N+1)(e)x equals "
                + "((e+2)/2)*C_N(e+2)x minus (J_tau(collisionField_N)).coeff e x, "
                + "plus Q(tau)/2 times C_N(e+2)x, plus B/2 times the finite sum over "
                + "j<=N of r_j*C_(N-j)(e+2*(j+1))x. The scalar recurrence follows from "
                + "power-series differentiation and the inverse square-root unit. The current "
                + "moment calculation differentiates the actual translated input polynomial. "
                + "Every interchange of coefficient sums uses finite support for the input "
                + "after the relevant transformation.")),
            Paragraph(Text("The corrected source sequence satisfies the same recurrence through "
                + "physical translation, actual annihilation on creation coefficients and the "
                + "negative-current insertion formula. Current zero mode, singleton and pair "
                + "corrections and their one-half factors remain in the calculation. At N=0, "
                + "Corr(1) is the empty correction, the scalar coefficient is one, the two "
                + "creation exponentials multiply to the exponential for sigma+tau and the "
                + "pair translation restricts to the diagonal. Strong induction therefore "
                + "compares every signed coefficient on every actual input. Its induction "
                + "property quantifies over all transformed inputs, so it also transports "
                + "the entire current insertion field.")),
            Paragraph(Text("For the ordinary source product, mode r of the sigma ground source "
                + "on the tau ground source is epsilon D sigma tau times the source with "
                + "charge sigma+tau and creation degree -r-1-B. Negative degrees vanish. "
                + "For a nonnegative degree, its corrected coefficient is epsilon D sigma tau "
                + "times the corresponding collision coefficient. The fixed chargeScalar "
                + "and chosen ground action remain those of the actual corrected field. "
                + "The quadratic identity Q(sigma+tau)=Q(sigma)+Q(tau)+2*B proves "
                + "c_sigma*c_tau*2^(-2*B)=c_(sigma+tau) using signed powers of the nonzero "
                + "scalar two. The chosen ground product is epsilon(sigma,tau) times "
                + "groundAction(sigma+tau). Consequently the same complete coefficient is "
                + "c_sigma*c_tau*2^(-2*B) times the tensor map with collisionOscillator and "
                + "groundAction(sigma)*groundAction(tau), for every actual tensor input.")),
            Paragraph(Text("The proof uses the repository's actual annihilation, finite correction, "
                + "negative-current insertion, physical translation and charged product kernel "
                + "constructions. This is an algebraic half-Fock coefficient comparison. "
                + "The complete charged residue law, an independently unweighted outer tail, "
                + "finite inversion and arbitrary-source Borcherds reconstruction remain further "
                + "obligations. The full Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT "
                + "programme remains incomplete.")))));
}
