using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class ExponentialKernelRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cardinal dimension of the complete row space adds across distinct exponential blocks.",
        H("Exact addition of exponential kernel block ranks"),
        Blocks(Describe.Lean(DescribeId.Create("entire-exponential-kernel-rank-addition"),
            DeclarationHandle.Create("D5/S3/Analytic/Entire/ExponentialKernelRank.exponential_kernel_row_rank_additive"),
            H("Cardinal rank addition for actual section spaces"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite injective family of arbitrary complex exponents and arbitrary complex polynomials, the Cardinal Module.rank of the row space of the weighted Hankel kernel of their sum equals the Cardinal sum of the corresponding individual block row ranks. The row space is the span of all actual sections on the whole complex plane. Zero blocks and the empty family remain included.")),
                Paragraph(Text("For a finitely separated kernel, applying any algebraic linear functional in one variable produces a member of its opposite section span. The proof uses the full algebraic double-annihilator identity and a finite separated expansion. This is what justifies using the algebraic block projections without assuming continuity of those projections or Fock membership of arbitrary entire factors.")),
                Paragraph(Text("Right block projections put every individual block section inside the total row space. Left projections select that block and kill the others, making the summation map from the finite product of the actual block row spaces injective. Every total section is the sum of its actual block sections, so that map is also onto. The resulting linear equivalence gives exact Cardinal rank addition. The physical operator range continues to use its own Cardinal rank; the completed rank/separation theorem supplies the physical connection."))),
            DescribeRole.Theorem))));
}
