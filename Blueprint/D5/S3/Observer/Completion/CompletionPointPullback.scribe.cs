using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class CompletionPointPullbackDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/CompletionPointPullback."
            + "zero_set_pullback";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completion points pull back exactly along a change of state representation.",
        H("Completion Point Pullback"),
        Blocks(Describe.Lean(
            DescribeId.Create("completion-point-pullback"),
            DeclarationHandle.Create(Declaration),
            H("Completion Point Pullback"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A change of state representation induces a pulled-back defect by function composition.")),
                Paragraph(Text(
                    "Its completed locus is precisely the preimage of the original completed locus."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("pulled_back_zero_set"), Sp, Rightarrow, Sp,
            F.Id("preimage_of_zero_set"), Dot));
}
