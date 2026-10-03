using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfAvoidanceCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/ZeckendorfAvoidanceCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional weighted avoidance count.",
        H("Conditional weighted avoidance count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorfavoidancecount-legalwords"),
                DeclarationHandle.Create(Prefix + "legalWords"),
                H("Legal words with an entering bit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("legalWords 0 b = [[]]. For n + 1, legalWords (n + 1) b lists the words 0 :: w for w in legalWords n 0, followed, when b = 0, by 1 :: w for w in legalWords n 1. It enumerates words of the specified length for which b :: w has no adjacent ones."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfavoidancecount-endbit"),
                DeclarationHandle.Create(Prefix + "endBit"),
                H("Final bit with empty-word convention"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("endBit b [] = b and endBit b (a :: w) = endBit a w. The entering bit is retained for an empty word; otherwise this is the last input bit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfavoidancecount-endpointweight"),
                DeclarationHandle.Create(Prefix + "endpointWeight"),
                H("Perron endpoint weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For b : Fin 2, endpointWeight b is Real.goldenRatio if b = 0 and 1 otherwise. The endpoint weight retains the last bit when successive legal blocks are counted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfavoidancecount-blockwords"),
                DeclarationHandle.Create(Prefix + "blockWords"),
                H("Aligned block avoidance with a short suffix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("blockWords r 0 b = legalWords r b. For k + 1, blockWords r (k + 1) b concatenates each p in legalWords 14 b with p ≠ B1 to every word in blockWords r k (endBit b p). These length-14k+r words avoid B1 at the aligned block positions; words avoiding B1 everywhere form a subset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfavoidancecount-1"),
                DeclarationHandle.Create(Prefix + "uniform_avoidance_count"),
                H("Conditional weighted avoidance count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem uniform_avoidance_count (H : ℕ) : ((legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))).length ≤ Real.goldenRatio ^ (H + 1) * (1 - (Real.goldenRatio ^ (14 : ℕ))⁻¹) ^ (H / 14)`.")),
                    Paragraph(Text("Legal words avoiding 00010101001000 have count at most φ^(H+1)(1−φ^(−14))^floor(H/14). Endpoint weights φ and 1 retain the entering bit across each 14-block. Removing the allowed block under either entering state gives the uniform conditional transfer loss; the final short suffix is counted explicitly."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfContextualReplacement"))]));
}
