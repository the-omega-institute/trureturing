using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMScoreSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact symmetries of the centered original EJM local blocks.",
        H("Local coordinate permutations and outcome relabelings"),
        Blocks(
            Paragraph(Text("The ten-coordinate triangle and nine-coordinate singleton blocks use their actual 12 local coordinate permutations. Reindexing the exact head-outcome sums proves the centered-block symmetries. The actual F1 and F2 coefficient invariances then supply the score-preservation facts consumed by local row bounds and cache association.")),
            Describe.Lean(DescribeId.Create("triangle-coordinate"),
                DeclarationHandle.Create(Prefix + "triangleCentered_coordinate"),
                H("Triangle-block coordinate symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full centered triangle block inherits the 12 local coordinate symmetries of its coefficient function. The head outcome sum is reindexed by the induced identity or A,B swap."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-coordinate"),
                DeclarationHandle.Create(Prefix + "singletonCentered_coordinate"),
                H("Singleton-block coordinate symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The centered singleton block inherits each local coordinate symmetry. The singleton coordinate is fixed and the other eight coordinates are permuted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-relabel"),
                DeclarationHandle.Create(Prefix + "triangleCentered_relabel"),
                H("Triangle-block outcome symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common outcome bijection preserving the coefficient function also preserves its centered triangle block, including its weighted head contraction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-relabel"),
                DeclarationHandle.Create(Prefix + "singletonCentered_relabel"),
                H("Singleton-block outcome symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reindexing the singleton outcome sum transports coefficient relabeling invariance to the entire centered singleton block."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-triangle-coordinate"),
                DeclarationHandle.Create(Prefix + "actual_triangleCentered_coordinate"),
                H("Actual triangle-block coordinate symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual F1 lookup supplies the local coordinate invariance consumed by the triangle partial-state bound replay."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-singleton-coordinate"),
                DeclarationHandle.Create(Prefix + "actual_singletonCentered_coordinate"),
                H("Actual singleton-block coordinate symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual F2 lookup supplies the local coordinate invariance consumed by the singleton partial-state bound replay."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-triangle-relabel"),
                DeclarationHandle.Create(Prefix + "actual_triangleCentered_relabel"),
                H("Actual triangle-block outcome symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every common outcome bijection preserves the actual centered triangle block. The finite bound replay uses this fact to work with canonical equality patterns."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-singleton-relabel"),
                DeclarationHandle.Create(Prefix + "actual_singletonCentered_relabel"),
                H("Actual singleton-block outcome symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every common outcome bijection preserves the actual centered singleton block, supplying the outcome-symmetry premise for its partial-state replay."))), DescribeRole.Theorem))));
}
