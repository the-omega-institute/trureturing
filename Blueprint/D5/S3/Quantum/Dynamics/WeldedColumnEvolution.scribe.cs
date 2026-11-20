using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class WeldedColumnEvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary-tree column sizes and neighbor counts determine the exact compressed walk.",
        H("Column evolution with a central weld"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("central-defect-column-evolution"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/WeldedColumnEvolution.central_defect_column_evolution"),
                H("Normalized columns and endpoint evolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Eigenstructure/childs2003gluedtrees")),
                Blocks(
                    Paragraph(Text(
                        "Let a finite simple graph have columns numbered from zero to 2d+1. " +
                        "Column j has size two raised to the smaller of j and 2d+1-j. " +
                        "Assume the following neighbor counts at each actual vertex. Its neighbors " +
                        "lie in the adjacent columns. From column i to i+1 the count is two for " +
                        "i at most d and one for i greater than d. In the reverse direction " +
                        "from i+1 to i it is one for i below d and two for i at least d.")),
                    Paragraph(Text(
                        "Take the graph adjacency divided by the square root of two as the graph " +
                        "Hamiltonian. Put the normalized column indicators in the columns of Q. " +
                        "The resulting weighted path has unit nearest-neighbor weights and a " +
                        "central edge of weight square root of two. For every real time t, the " +
                        "indicators are orthonormal, and the actual matrix exponentials of minus " +
                        "i times t times the two Hamiltonians intertwine through Q. The graph " +
                        "exponential entry from the first singleton column to the last equals " +
                        "the endpoint entry of the path exponential.")),
                    Paragraph(Text(
                        "Childs et al., Section III.C, equations (25)–(27), give the column " +
                        "model. The neighbor counts act on the normalized indicators with the factor " +
                        "given by the ratio of adjacent square-root sizes. The resulting " +
                        "rectangular matrix identity lifts to the exponential using a block " +
                        "diagonal matrix and its commuting off-diagonal block."))),
                DescribeRole.Theorem))));
}
