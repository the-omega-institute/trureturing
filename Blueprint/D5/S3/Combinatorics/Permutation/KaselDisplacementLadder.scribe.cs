using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class KaselDisplacementLadderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kasel's displacement ladder equals m minus two at every horizon four to the m, for m at least two.",
        H("Kasel's displacement ladder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kasel-displacement-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The exact displacement-ladder claim"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural m at least two, there exist natural-valued stage and "
                    + "fibre-position functions s and r that form a valid normalized scheme on "
                    + "SA m, and s(v) is at most floor(block(v)/2) plus m minus two for every "
                    + "distinguished value v. Conversely, every valid normalized scheme on "
                    + "SA m has a distinguished value v with s(v) at least floor(block(v)/2) "
                    + "plus m minus two. Thus the minimum over schemes of the maximum "
                    + "distinguished displacement is L(m)=m-2 at horizon 4^m."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kasel-displacement-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Kasel's conjectured growth is proved"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The upper construction puts 3 and 4 at stage one and every other "
                    + "value at stage m, ordered within parity by target-biased binary reversal. "
                    + "It proves injectivity, normalization and avoidance of both monotone "
                    + "three-term arithmetic progressions. The lower bound converts the "
                    + "concatenation order into predecessor ranks and applies the frozen "
                    + "Erdos-Graham order-gadget obstruction at scale 2*4^(m-1); the case "
                    + "m=2 follows from normalization. Combining these bounds proves claim. "
                    + "This resolves the displacement-ladder conjecture in Appendix B.4, "
                    + "while the parent Erdos Problem 197 remains open."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kasel-2026-displacement-ladder"), ResolutionKind.Proved))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/Permutation/KaselDisplacementLadderLower")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/Permutation/KaselDisplacementLadderUpper"))]));
}
