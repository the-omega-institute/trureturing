using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.IntervalObstruction;

internal sealed class IntervalObstructionBasicDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict all-time forward Bowen bounds, exact interval pullbacks and monotone trapping.",
        H("IntervalObstruction - Basic"), Blocks(
        Describe.Lean(DescribeId.Create("forward-bowen"), DeclarationHandle.Create(Owner + "ForwardBowen"),
            H("Strict forward Bowen sets"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("ForwardBowen f epsilon x contains precisely those y for which dist(f^t(x), f^t(y)) < epsilon at every natural t, including zero. ForwardBowenBound uses encard, so an infinite set cannot satisfy a finite bound. FinitelyPositiveExpansive chooses one epsilon > 0 and one natural N >= 1 before every center."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("selected-pullback"), DeclarationHandle.Create(Owner + "exact_pullback"),
            H("Exact selected interval pullbacks"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A continuous map on a nondegenerate closed real interval has a selected nondegenerate closed subinterval mapping exactly onto each nondegenerate closed target interval contained in its image. The proof selects the first upper-level hit and the last lower-level hit; it does not identify the entire inverse image with an interval."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("small-monotone-interval"), DeclarationHandle.Create(Owner + "strictly_monotone_small_segment"),
            H("All-time small intervals for monotone dynamics"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a continuous strictly increasing or strictly decreasing interval self-map, every positive requested scale admits a nondegenerate subinterval whose images have smaller diameter at every forward time. Monotone bounded orbits have vanishing successive gaps; the decreasing-map case uses the square and controls all odd times by compact uniform continuity. These constructions are used by the obstruction and its return-chain argument."))), DescribeRole.Theorem)))));
}
