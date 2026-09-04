using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class FoldDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.RvM.Ncount_eq_im_halfContour";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Functional-equation symmetry folds the full argument-principle contour.",
            H("Completed-Zeta Contour Fold"),
            Blocks(Describe.Lean(
                DescribeId.Create("fold"),
                DeclarationHandle.Create(Declaration),
                H("Completed-Zeta Contour Fold"),
                StatementSource.FromAuthor(Disp(F.Id("Fold"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Functional-equation symmetry folds the full argument-principle contour."))),
                DescribeRole.Theorem))));
    }
}
