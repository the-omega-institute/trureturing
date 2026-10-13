using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteSymmetryDAGReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteSymmetryDAGReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound bounded replay of shared branch shapes in every actual partial context.",
        H("The checker earns a global bound through actual lower bounds and rank-decreasing symmetries"),
        Blocks(
            Paragraph(Text("Node has bound, symmetry and split constructors, with one child index for every possible value at a split. The indexed node function may depend on the remaining fuel. Check recursively follows every value choice and carries the actual updated partial assignment along each edge. Fuel zero rejects even if a node index is reused or cyclic. Sharing an index saves branch data; it neither reuses a lower-bound calculation from a different assignment nor supplies a score-invariance or rank-decrease proof. An imported finite DAG becomes a certificate only after the full actual-context Boolean acceptance and every soundness premise are earned.")),
            Describe.Lean(DescribeId.Create("check"),
                DeclarationHandle.Create(Prefix + "check"),
                H("Fuel-bounded checking in the actual reached partial assignment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A bound node checks gap at most lower of the current partial event. A symmetry node checks strict-dominance evidence at that same partial event. A split checks every outcome child after setting the actual split coordinate to that outcome and decreasing fuel. The function returns a Boolean and does not prove its own acceptance or semantic soundness."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("expand"),
                DeclarationHandle.Create(Prefix + "expand"),
                H("The finite mathematical tree interpretation of shared branch data"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bounded expansion interprets each indexed node as a literal bound, symmetry or split tree and recursively expands each child. At fuel zero the interpretation is a bound tree, but the actual checker rejects fuel zero, so the acceptance-to-expansion proof cannot obtain an unchecked leaf from exhausted fuel."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("global-bound"),
                DeclarationHandle.Create(Prefix + "checked_global_lower_bound"),
                H("Accepted shared-shape replay bounds every full event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume every actual lower function value bounds the score of every compatible completion, every supplied action preserves the original score, and every successful dominance check strictly decreases the supplied natural-number rank for every compatible completion. Full checker acceptance from the given root, fuel and all-unknown assignment then yields gap at most score for every full event. The private induction transports actual acceptance to the expanded literal tree before applying the established exhaustive-tree soundness. All three semantic premise families and concrete full replay acceptance remain necessary; literal data, one successful leaf or external validation cannot replace them."))),
                DescribeRole.Theorem))));
}
