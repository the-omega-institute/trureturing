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
                Blocks(Paragraph(Text("For natural parameters n and r, bseq starts at one and its coefficient m plus one is r times n plus 2 times m plus one minus 2, times coefficient m, divided by 2 times m plus one. All arithmetic in this recurrence after coercion is real arithmetic."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-chs-interface-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_zero"),
                H("The initial comparison coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For all natural n and r, bseq n r 0 equals one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-chs-interface-3"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_succ"),
                H("The successor recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For all natural n, r and m, 2 times m plus one times bseq n r at m plus one equals r times n plus 2 times m plus one minus 2 times bseq n r m. Parentheses around m plus one are retained in each factor."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-chs-interface-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_recurrence"),
                H("The positive-index recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For all natural n, r and m with m at least one, 2m times bseq n r m equals r times n plus 2m minus 2 times bseq n r at m minus one. The factor n plus 2m minus 2 is evaluated in the real numbers."))), DescribeRole.Theorem))));
}
