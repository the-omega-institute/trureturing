using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RegularCHS;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete homogeneous symmetric adjacency coefficients.",
        H("Defs"), Blocks(
            Describe.Lean(DescribeId.Create("regular-chs-defs-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Defs.adjMatrix_isHermitian"),
                H("Real adjacency matrices are Hermitian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For every natural n and simple graph G on Fin n, the real adjacency matrix is Hermitian. Symmetry of graph adjacency supplies the matrix symmetry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-chs-defs-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Defs.chs"),
                H("Adjacency complete homogeneous coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For every graph G on Fin n and natural degree d, chs G d is the complete homogeneous symmetric polynomial hsymm of degree d evaluated at the real eigenvalues of the adjacency matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-chs-defs-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Defs.chsNorm"),
                H("Adjacency CHS norms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For every graph G and natural degree d, chsNorm G d is the real power of chs G d with exponent one divided by d. The extremal claim uses only positive even degrees."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-chs-defs-3"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Defs.claim"),
                H("Extrema over connected regular graphs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For every n at least three and m at least one, both the cycle and the complete graph on Fin n are connected and regular, and every connected regular graph G on Fin n has its degree 2m CHS norm between those of the cycle and the complete graph. The word connected has the usual graph theoretic meaning."))), DescribeRole.Definition))));
}
