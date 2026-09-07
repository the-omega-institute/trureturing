using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.GoldenRecovery;

internal sealed class GoldenFactorSecondOrderBinomialRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed-length golden factor and its true-count/scattered-pair profile have the same observation fibers.",
        H("Golden Factor Binomial Recovery"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("golden-factor-second-order-binomial-rigidity-source"),
                DeclarationHandle.Create("D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_factor_eq_iff_second_order_profile_eq"),
                H("Source-linked mathematical interpretation"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The fixed-length golden factor and its true-count/scattered-pair profile have the same observation fibers.")),
                    Paragraph(Text("This specializes classical Sturmian binomial rigidity using the frozen Beatty-window owner. It recovers word contents rather than occurrence positions.")),
                    Paragraph(Text("This mirror supplies commentary only. The named Lean declaration and its kernel report own the exact statement and verification status.")))))));
}
