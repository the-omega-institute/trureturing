using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicTetranacciDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicTetranacci.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic avoidance numbers for 4123 and 1324 follow the Tetranacci sequence.",
        H("Tetranacci Enumeration of Cyclic Avoiders"),
        Blocks(
            Describe.Lean(DescribeId.Create("archer-cyclic-tetranacci-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The Tetranacci enumeration"),
                StatementSource.FromAuthor(Disp(F.Id("tetranacciClaim"))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive n, the number of cyclic permutations avoiding 4123 in one-line form and 1324 in every cycle form equals the Tetranacci number at index n plus two."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("archer-cyclic-4123-1324-tetranacci"), ResolutionKind.Proved))),
        []));
}
