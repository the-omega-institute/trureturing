using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The (32; 1 to 3) avoidance series satisfies a cubic equation and is its distinguished formal branch.",
        H("Enumeration of (32; 1 to 3) Avoiders"),
        Blocks(
            Describe.Lean(DescribeId.Create("arrow-thirty-two-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The cubic enumeration"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The generating series F of the (32; 1 to 3) avoidance numbers satisfies 1 + (3x - 2)F + (1 - x)(1 - 2x)F squared + x cubed F cubed = 0. It is the unique integer formal power series satisfying this equation with constant coefficient one and coefficient of x equal to one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("zhou-yu-arrow-32-13-enumeration"), ResolutionKind.Proved))),
        []));
}
