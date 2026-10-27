using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class LaguerreSevenHalfMellinAbsoluteBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMellinAbsoluteBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear absolute central Mellin control",
        H("Linear absolute central Mellin control"),
        Blocks(
            Paragraph(Text("These supplier proofs are reused from commit 73c64f70, with its actual Laguerre definitions and upstream attribution. The inverse moment controls the near-origin part; the physical Jacobi multiplication recurrence controls the tail. Both controls are proved, not assumed.")),
            Describe.Lean(
                DescribeId.Create("laguerre-seven-half-mellin-absolute-integrable"),
                DeclarationHandle.Create(Owner + "centralPsi_integrable_absolute_mellin"),
                H("Absolute Mellin integrability"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n, x^(5/4) times the absolute value of the actual normalized mode is integrable on x>0. This is consumed by both the mode bound and the physical synthesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laguerre-seven-half-mellin-linear-bound"),
                DeclarationHandle.Create(Owner + "centralPsi_absolute_mellin_le"),
                H("A uniform linear bound for every mode"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n, the absolute central Mellin integral is at most 10(n+1). Splitting at one and applying scaled square estimates yields the stated bound from the exact inverse moment and the quadratic graph moment. This controls the infinite weighted coefficient synthesis without postulating a continuous Mellin functional."))),
                DescribeRole.Theorem))));
}
