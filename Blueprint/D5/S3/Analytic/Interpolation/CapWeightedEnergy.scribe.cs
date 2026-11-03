using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class CapWeightedEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An essential cap and an integrable weighted quadratic energy imply Bochner integrability and an optimized inverse-power integral bound in every complete real normed space.",
        H("Cap-sensitive weighted-energy interpolation"),
        Blocks(
            Paragraph(Text("Let E be any complete real normed space. All integrals use Lebesgue measure on the positive real half-line. Assume 0<alpha<1, B>=0 and delta>=0. The map w from the real line to E is almost everywhere strongly measurable on that half-line, its norm is at most B almost everywhere, and the actual nonnegative energy t times the square of its norm is integrable with integral at most delta. No integrability of the inverse-power weighted vector is assumed.")),
            Describe.Lean(
                DescribeId.Create("cap-weighted-energy-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CapWeightedEnergy.sharpConstant"),
                H("The optimized coefficient"),
                StatementSource.FromAuthor(Disp(Seq(Call("K", A), Eq,
                    Frac, Grp(D(1)), Grp(D(1), Minus, A),
                    new Formula.Power(Seq(Frac, Grp(A, Plus, D(1)), Grp(D(2), A)),
                        Seq(Frac, Grp(A, Plus, D(1)), Grp(D(2))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The definition is total on real alpha. Its use in the estimate requires 0<alpha<1; in this range the coefficient is finite and positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cap-energy-near-power-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CapWeightedEnergy.power_integral_near"),
                H("The integrable near power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real alpha<1 and a>0, t^(-alpha) is integrable on (0,a] and its integral is a^(1-alpha)/(1-alpha). This Mathlib application is a consumed auxiliary result for the interpolation estimate and its scalar equality profile."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cap-energy-tail-power-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CapWeightedEnergy.power_integral_tail"),
                H("The integrable tail power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real alpha>0 and a>0, t^(-2alpha-1) is integrable on (a,infinity) and its integral is a^(-2alpha)/(2alpha). This consumed auxiliary result reuses Mathlib's improper power integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cap-energy-near-linear-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CapWeightedEnergy.linear_integral_near"),
                H("The near linear energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a>0, the identity function is integrable on (0,a] and its integral is a^2/2. The interpolation and scalar equality-profile proofs consume this direct Mathlib application."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cap-weighted-energy-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CapWeightedEnergy.norm_integral_le_sharp_cap_energy"),
                H("The inverse-power Bochner estimate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("norm", Call("integral", Call("inversePowerWeightedVector", A, W))), Le,
                    Call("K", A), new Formula.Power(B, A), new Formula.Power(Dl,
                        Seq(Frac, Grp(D(1), Minus, A), Grp(D(2))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every E and w under all assumptions stated above, the function t to t^(-alpha) times w(t) is Bochner integrable on (0,infinity), and the norm of its integral is at most K(alpha) B^alpha delta^((1-alpha)/2). The integrability conclusion is part of the result, so a nonintegrable Bochner integral's default zero cannot establish the claim.")),
                    Paragraph(Text("For B and delta positive choose a>0 with delta=B^2 a^2(alpha+1)/(2alpha), and lambda=1/(2B a^(alpha+1)). Put f(t)=norm(w(t)). On 0<t<=a, the cap gives t^(-alpha)f(t)<=lambda t f(t)^2+B t^(-alpha)-lambda B^2 t. On t>a, the square (2lambda t f(t)-t^(-alpha))^2 gives t^(-alpha)f(t)<=lambda t f(t)^2+(4lambda)^(-1)t^(-2alpha-1). Both majorants are genuinely integrable. Their exact integrals, followed by the energy budget and the chosen cutoff, give the coefficient. If B=0 or delta=0 then w vanishes almost everywhere and the same conclusion follows.")),
                    Paragraph(Text("The power-integral and Bochner-measure infrastructure is reused from the pinned Mathlib. The cap-sensitive quadratic optimization is the new formal proof here. The scalar profile B min(1,(a/t)^(alpha+1)) identifies the abstract equality profile; this does not claim that any particular resolvent family attains it. No literature novelty or optimal quantum-resolvent constant is asserted."))),
                DescribeRole.Theorem))));

    private static Formula A => F.Id("alpha");
    private static Formula B => F.Id("B");
    private static Formula Dl => F.Id("delta");
    private static Formula W => F.Id("w");
}
