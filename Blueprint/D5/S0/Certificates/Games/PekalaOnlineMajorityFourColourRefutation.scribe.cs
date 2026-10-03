using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class PekalaOnlineMajorityFourColourRefutationDocument
    : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pekala2026onlinemajority");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four colours cannot guarantee online majority edge-colouring for every order from five to seven.",
        H("Online majority edge-colouring at five to seven vertices"),
        Blocks(
            Paragraph(Text(
                "Pekala's Problem 11 asks whether Algorithm can use at most four colours "
                    + "against every Presenter strategy for final simple graphs on "
                    + "n in {5,6,7} vertices with minimum degree exactly two. The formal "
                    + "claim is the joint affirmative assertion for those three orders.")),
            Describe.Lean(
                DescribeId.Create("pekala-online-majority-four-colour-result"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation.result"),
                H("No joint four-colour online strategy"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "A Lean-checked adaptive Presenter certificate on five vertices "
                            + "covers every normalized four-colour response. Each leaf "
                            + "has final minimum degree exactly two and a strict majority "
                            + "violation. This refutes the joint affirmative claim.")),
                    Paragraph(Text(
                        "For six or seven vertices, continue each bad five-vertex play "
                            + "by connecting every new vertex to two old vertices other "
                            + "than a vertex where majority already fails. Each new vertex "
                            + "then has degree two, and the old violation survives all "
                            + "new colour choices. This extension answers each listed "
                            + "order negatively; it is a separate combinatorial argument."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pekala-online-majority-four-colours"),
                    ResolutionKind.Refuted)))));
}
