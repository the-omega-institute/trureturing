using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AbelianBorders;

internal sealed class AbelianBorderQuestionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AbelianBorders/AbelianBorderQuestion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/charlier2015abelianbordered");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit ternary word gives a negative answer to Question 2 of Charlier, Harju, Puzynina, and Zamboni.",
        H("Weak Abelian Periodicity Does Not Force Finitely Many Unbordered Factors"),
        Blocks(
            Node("question-two-refuted", "Question 2 has a negative answer", "result",
                ResultFormula(),
                "The ternary word has a bounded decomposition into equal-frequency blocks and satisfies "
                    + "the cylinder and tangential-line conditions, yet it has infinitely many nonempty weakly "
                    + "abelian unbordered factors. This answers Question 2 negatively even when the suffix of a "
                    + "border may be the entire word.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ResultFormula() =>
        Disp(Negated(F.Id("claim")));

    private static Formula Negated(Formula value) => new Formula.Not(Seq(Open, value, Close));
}
