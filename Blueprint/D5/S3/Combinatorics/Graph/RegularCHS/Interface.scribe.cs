using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RegularCHS;

internal sealed class InterfaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete homogeneous symmetric adjacency coefficients.",
        H("Interface"), Blocks(
            Describe.Lean(DescribeId.Create("regular-chs-interface-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Interface.closedWalks"),
                H("Rooted closed walk counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For a simple graph G on Fin n and natural length k, closedWalks G k is the natural sum of the diagonal entries of the kth power of its natural adjacency matrix. Length zero is included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-chs-interface-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq"),
                H("The even comparison coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For natural n and r, write b(m) for bseq n r m. Then b(0)=1 and b(m+1)=r*(n+2*(m+1)-2)*b(m)/(2*(m+1)) for every natural m. The numerator and denominator are evaluated in the real numbers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-chs-interface-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_zero"),
                H("The initial comparison coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For all natural n and r, bseq n r 0 equals one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-chs-interface-3"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_succ"),
                H("The successor recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For all natural n, r and m, write b(k) for bseq n r k. The identity is 2*(m+1)*b(m+1)=r*(n+2*(m+1)-2)*b(m), with all scalar arithmetic in the real numbers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-chs-interface-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_recurrence"),
                H("The positive-index recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For natural n, r and m with m at least one, write b(k) for bseq n r k. The identity is 2*m*b(m)=r*(n+2*m-2)*b(m-1). The scalar factors use real arithmetic and the coefficient index m-1 uses natural subtraction."))), DescribeRole.Theorem))));
}
