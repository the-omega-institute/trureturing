using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfEquivalence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The avoidance classes of the two three-letter arrow patterns have equal cardinality in every positive degree.",
        H("The Arrow-Wilf Equivalence"),
        Blocks(Node("arrow-wilf-equivalence", "The two patterns are equinumerous", "result",
            Disp(F.Id("claim")),
            "For each positive n, the two avoidance counts equal the respective finite formulas F1(n) and F2(n). Their correction terms both equal the same finite signed sum E(n), so the cardinalities agree.",
            DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("zhou-yu-arrow-wilf-equivalence"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);
}
