using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class PairedLaplaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A logarithmic forward response has a paired Laplace expansion with a holomorphic quadratic-growth remainder.",
        H("The paired Laplace representation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("laplace-forwardlog-eq-forwardmellin"),
                DeclarationHandle.Create(Prefix + "laplace_forwardLog_eq_forwardMellin"),
                H("Logarithmic coordinates recover the forward Mellin transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a cutoff x0 at least three, the Laplace transform of the forward response written in logarithmic coordinates equals the forward Mellin transform starting at x0. The change of variables x=exp(y) preserves the complete response and handles the cutoff by an indicator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-regular-part-holomorphic"),
                DeclarationHandle.Create(Prefix + "forwardRegularPart_holomorphic"),
                H("The regular part is holomorphic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the Mellin remainder is differentiable on the half-plane Re(s)>-1/5, then adding the elementary pole, logarithmic, and digamma terms produces a function differentiable on that same half-plane."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-regular-part-growth"),
                DeclarationHandle.Create(Prefix + "forwardRegularPart_growth"),
                H("Quadratic growth of the regular part"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A quadratic vertical-strip bound for the Mellin remainder implies a quadratic bound for the regular part on |Re(s)|<=1/20. The digamma estimate, logarithm bound, and the elementary denominator are absorbed into one nonnegative constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-paired-laplace-data"),
                DeclarationHandle.Create(Prefix + "forwardPairedLaplaceData"),
                H("The forward response supplies paired Laplace data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the Riemann hypothesis, a von Koch error bound, and the paired xi expansion, the logarithmic forward response is measurable, locally bounded, initially convergent, and has a holomorphic regular part with quadratic growth. In the strip 1/2<Re(s)<1 its Laplace transform equals minus one half of the paired zeta-zero pole sum plus that regular part."))),
                DescribeRole.Definition))));
}
