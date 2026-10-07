using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PackingDomatic;

internal sealed class PackingDomaticPathDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/bresar2026packingdomatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The path on 56 vertices refutes the proposed bound for packing 28-domatic colourings.",
        H("A Negative Answer to Problem 2"),
        Blocks(
            Node("problem-two-refuted", "Some paths require more than k+1 colours", "result",
                ResultFormula(),
                "Take k=28 and n=56. A packing 28-domatic colouring using colours at most 29 would "
                    + "satisfy the counting bound, since 30 is at most 56. That bound would require "
                    + "448 to be at most 447, a contradiction. Thus P_56 has no such colouring, and "
                    + "the proposed bound fails despite k being at least 3 and n being at least 2k.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bresar-ferme-hu-packing-domatic-paths"), ResolutionKind.Refuted)))));

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
        Disp(new Formula.Not(Seq(Open, F.Id("claim"), Close)));
}
