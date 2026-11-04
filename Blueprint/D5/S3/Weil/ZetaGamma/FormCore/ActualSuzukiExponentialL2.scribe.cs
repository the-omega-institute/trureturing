using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiExponentialL2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original H6 pays the actual critical exponential B domain",
        H("Original H6 pays the actual critical exponential B domain"),
        Blocks(
            Paragraph(Text("The original F is preserved through fullTheta, actualGammaProfile and actualSuzukiEvenBProfile. The physical H6 budget alone supplies this exponential domain. It supplies neither the logarithmic Fourier budget nor the nonpositive complete-energy hypothesis used separately in W366. No RH, Robin inequality, density, or global Riemannian completeness conclusion is asserted.")),
            Describe.Lean(
                DescribeId.Create("right-tail-increasing-exponential-conjugation"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.right_exponential_tail_exponential_conjugation"),
                H("Increasing weights raise the future-tail decay rate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual integral, exp(a t) R_k u(t)=R_(k+a)(exp(a .)u)(t). The rate is k+a. In the critical Suzuki application k=a=5/4, so the weighted tail has rate 5/2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-h6-critical-gamma-domain-mass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.actual_h6_gamma_profile_critical_exponential_l2_and_mass"),
                H("The same actual Gamma profile has its critical weighted domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the original physical H6 source F, exp(5t/4) actualGammaProfile(F,t) is in L2 on t>0. Its squared mass is exactly pi^(-5/2) times integral_(x>pi) x^6 |fullTheta(F,x)|^2. This is a half-line input to B, and its identity keeps the complete theta transform of this same F."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-h6-actual-even-b-critical-budget"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.actual_h6_suzuki_even_b_l1_l2_critical_exponential"),
                H("The actual even-B profile has both L2 domains and an original-source budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same original H6 source F, its actual full-line even-B profile is in L1 and L2, and exp(5|r|/2) times that profile is in L2. The last squared mass is at most (68/25) pi^(7/2) (sum_(n>=1) n^(-3))^2 times integral_(x>pi) (x/pi)^6 |F(x)|^2. The nonoptimal factor 68/25 comes from 2|v|^2+(9/2)|R_(5/2)v|^2 and the global tail L2 bound. The existing private total sixth-moment theta norm estimate is consumed directly. Under t=2|r|, the two real half-lines cancel the Jacobian; no extra factor 2 occurs."))),
                DescribeRole.Theorem))));
}
