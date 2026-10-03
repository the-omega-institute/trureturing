using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovan.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic avoidance numbers for 4132 and 1324 follow a subsequence of the Padovan numbers.",
        H("Padovan Enumeration of Cyclic Avoiders"),
        Blocks(
            Describe.Lean(DescribeId.Create("archer-cyclic-padovan-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The Padovan enumeration"),
                StatementSource.FromAuthor(Disp(F.Id("padovanClaim"))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive n, the number of cyclic permutations avoiding 4132 in one-line form and 1324 in every cycle form equals the Padovan number at index three times n."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("archer-cyclic-4132-1324-padovan"), ResolutionKind.Proved))),
        []));
}
