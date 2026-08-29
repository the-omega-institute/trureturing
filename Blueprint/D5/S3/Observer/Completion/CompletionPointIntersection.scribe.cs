using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class CompletionPointIntersectionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/CompletionPointIntersection."
            + "paired_zero_set_eq_intersection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired zero-defect completion equals intersection of component completion conditions.",
        H("Completion Point Intersection"),
        Blocks(Describe.Lean(
            DescribeId.Create("completion-point-intersection"),
            DeclarationHandle.Create(Declaration),
            H("Completion Point Intersection"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Two defect coordinates may be combined into one product-valued defect.")),
                Paragraph(Text(
                    "The product defect vanishes exactly when both coordinates vanish, so its zero set is their intersection."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("paired_defect_is_zero"), Sp, Rightarrow, Sp,
            F.Id("both_component_defects_are_zero"), Dot));
}
