using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class DefectDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Lipschitz update splits the total projection defect into two component defects.",
        H("Defect Decomposition for Projected Updates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-lipschitz-update-splits-the-total-projection-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/DefectDecomposition.defect_decomposition"),
                H("A Lipschitz update splits the total projection defect"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("E"), Comma, Esc,
                    F.Id("d"), Open,
                    F.Id("projectOutput"), Open,
                    F.Id("updateHigh"), Open, F.Id("diagHigh"), Open, F.Id("E"), Close, Close,
                    Close, Comma, Sp,
                    F.Id("updateLow"), Open,
                    F.Id("diagLow"), Open, F.Id("projectTable"), Open, F.Id("E"), Close,
                    Close, Close, Close, Sp, Leq, Sp,
                    F.Id("d"), Open,
                    F.Id("projectOutput"), Open,
                    F.Id("updateHigh"), Open, F.Id("diagHigh"), Open, F.Id("E"), Close, Close,
                    Close, Comma, Sp,
                    F.Id("updateLow"), Open,
                    F.Id("projectOutput"), Open, F.Id("diagHigh"), Open, F.Id("E"), Close,
                    Close, Close, Close, Sp, Plus, Sp,
                    F.Id("K"), Sp,
                    F.Id("d"), Open,
                    F.Id("projectOutput"), Open, F.Id("diagHigh"), Open, F.Id("E"), Close,
                    Close, Comma, Sp,
                    F.Id("diagLow"), Open, F.Id("projectTable"), Open, F.Id("E"), Close,
                    Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Insert the low-level update of the projected high-level diagonal between "
                        + "the projected high-level update and the low-level update of the "
                        + "projected table diagonal. The metric triangle inequality gives the "
                        + "two component distances, and the Lipschitz bound on the low-level "
                        + "update controls the second distance by K times the diagonal-projection "
                        + "defect."))),
                DescribeRole.Theorem))));
}
