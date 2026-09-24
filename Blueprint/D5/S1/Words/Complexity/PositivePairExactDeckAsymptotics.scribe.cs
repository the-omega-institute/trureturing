using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class PositivePairExactDeckAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairExactDeckAsymptotics";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite ordered alphabet of size at least two and every positive k, actual exact k-deck images have the full weighted-Lyndon Theta exponent.",
        H("Exact k-Deck Asymptotics"),
        Blocks(
            Paragraph(Text(
                "The lower estimate comes from actual equal-length positive-word constructions. "
                + "For the upper estimate, one singleton Lyndon coordinate is erased and recovered "
                + "from the fixed total source length; unconditional Lyndon-coordinate recovery "
                + "then identifies the complete exact deck. Thus exactly one degree of freedom is "
                + "removed, without an additional hypothesis on n or k.")),
            Describe.Lean(
                DescribeId.Create("actual-exact-deck-weighted-lyndon-theta"),
                DeclarationHandle.Create(Module + ".actual_exactKDeckImage_weightedLyndon_isTheta"),
                H("Full exact k-deck Conjecture 8.1 asymptotics"),
                StatementSource.FromAuthor(Disp(F.Id("actualexactKDeckImageweightedLyndonisTheta"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every finite linearly ordered type A with 2<=Fintype.card A, every k:N "
                    + "with 1<=k, the real-valued function n |-> (exactKDeckImage A k n).card is "
                    + "Real.IsTheta at Filter.atTop of n |-> (n:R)^(weightedLyndonExponent A k-1). "
                    + "Here weightedLyndonExponent is the weighted sum of the actual length-r "
                    + "Lyndon-word counts, so the theorem has all source quantifiers and no proxy "
                    + "parameter."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nilforoushan-parvaresh-conjecture-8-1"),
                    ResolutionKind.Proved))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/PositivePairExactDeckUpperBound"))]));
}
