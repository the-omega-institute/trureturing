using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalWiredSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A forced-open separator localizes the terminal connection bits to complementary variable edge families.",
        H("Two connection bits across a wired separator"),
        Blocks(
            Describe.Lean(DescribeId.Create("three-terminal-wired-touch-graph"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalWiredSeparation.touchGraph"),
                H("Edges touching a side"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any graph K and vertex set A, touchGraph K A retains exactly the actual "
                    + "K-edges with at least one endpoint in A."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("three-terminal-wired-separation"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalWiredSeparation.wired_separation"),
                H("Exact connection and partition localization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let H be a subgraph of K and K a subgraph of U. Let B be the H-connected component "
                    + "of b, assume that a and c lie outside B, and assume that U has no a-to-c path "
                    + "using only vertices outside B. Let A be the component of a in that restricted "
                    + "graph. Put L=H union touchGraph K A, and let R be H together with all K-edges "
                    + "whose endpoints both lie outside A. Then a and b are connected in K exactly "
                    + "when they are connected in L; b and c are connected in K exactly when they "
                    + "are connected in R; and a and c are connected in K exactly when those two "
                    + "connections both occur. The actual partition of K is therefore all, ab, bc, "
                    + "or separate according to the two bits, and cannot be ac. The variable edges "
                    + "retained on the two sides are complementary; their common H-edges are forced "
                    + "open. No finite-graph, cactus, or single-vertex-gate assumption is used. "
                    + "Every edge leaving A reaches B. Along a path from a, the first exit from A "
                    + "can be joined to b by H. Along a path from b, an exit from A can always be "
                    + "replaced by such an H-connection, yielding the two walk invariants."))),
                DescribeRole.Theorem)),
        []));
}
