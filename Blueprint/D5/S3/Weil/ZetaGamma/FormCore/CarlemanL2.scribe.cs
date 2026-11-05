using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class CarlemanL2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual absolute Carleman double-integral domain and pi bound on half-line L2 sources.",
        H("The literal Carleman double integral on arbitrary complex L2 sources"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-carleman-l2-domain"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaGamma/FormCore/CarlemanL2.carleman_actual_l2_domain"),
            H("The literal Carleman double integral on half-line L2"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For an arbitrary complex positive-half-line L2 input, the actual absolute Carleman double integral is finite and is bounded by pi times its L2 mass. There is no compact-support, continuity, trace, or pre-assumed double-integrability condition.")),
                Paragraph(Text("The proof derives the true row integral of sqrt(s)/(sqrt(t)*(s+t)) from the actual Cauchy integral and proves product-measure integrability of the Schur majorant before applying an integral inequality. This theorem is consumed by the half-rate Hankel domain proof."))),
            DescribeRole.Theorem))));
}
