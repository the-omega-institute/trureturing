using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OddModeStraighteningDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Borcherds rewrites on the actual negative twisted sector.",
        H("Local rewrites for the negative twisted sector"),
        Blocks(
            Entry("source-c2-expansion", "minusTwo_mem_of_pairs", "Expansion of a source C2 letter",
                "The finite iterate at p = 0 and r = -2 expands one source C2 letter into pairs whose mode indices "
                + "sum to the original index minus two."),
            Entry("adjacent-mode-swap", "swap_mem_iff", "Adjacent mode swap",
                "The finite commutator at r = 0 expresses the difference of adjacent orders through "
                + "nonnegative products in the fixed source."),
            Entry("duplicate-mode-elimination", "duplicate_mem_of_shorter_and_larger",
                "Elimination of a repeated mode index",
                "In the finite normal product, isolate the repeated pair in the first sum for a negative index "
                + "and in the second sum with exchanged inputs for a nonnegative index. Every other pair "
                + "has the same index sum and a strictly larger square sum."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
