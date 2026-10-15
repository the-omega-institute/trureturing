using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeOppositeCurrentInsertionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual one-current opposite insertion reverses composition only after the current zero correction is included.",
        H("Actual One-Current Opposite Insertion"),
        Blocks(
            Paragraph(Text("All operators act on the original unrestricted finite-support matter carrier. A denotes an actual neutral current; Y is the original reconstructed state-field. "
                + "The reflection identity separates the current-zero action from the positive-current tail. The term Y(A(0)b) combines with Y(b)A(0) through the existing actual zero-mode commutator. "
                + "This is necessary for charged states and does not use an invariant form or a generator-adjoint premise.")),
            Describe.Lean(DescribeId.Create("finite-finsum-zero-successor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.finsum_zero_succ"),
                H("Supported zero-term separation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual finite-support additive sequence, its supported sum is its zero term plus its successor tail. "
                    + "This separates the original current-zero term and shifts the finite first reversed sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-sum-successor-pair"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.sum_successor_pair"),
                H("Finite successor decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If f(0)=a(0) and f(j+1)=a(j+1)+b(j), then the sum through j=N is the sum of a through N plus the sum of b through N-1. "
                    + "This normalizes actual translated and current-inserted Sugawara descendants at a shared finite cutoff."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-current-one-reflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.current_one_reflection"),
                H("Zero-corrected actual current reflection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Y(A(-1)b)[p]v+Y(A(0)b)[p-1]v is the sum of A(-s)Y(b)[p+s-1]v for s>=0 and Y(b)[p-t-2]A(t+1)v for t>=0. "
                    + "Both orders are supported on the actual tested vector; the s=0 term is the corrected left current-zero action."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-opposite-current-one-insertion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.opposite_current_one_insertion"),
                H("Actual opposite insertion at frequency one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With both inverse-Gram equations, O_(A(-1)b)(n)v equals minus the first reversed sum O_b(n+t)A(t+1)v and minus the second reversed sum A(-s)O_b(n-s-1)v. "
                    + "The common finite descendant cutoff covers b and A(-1)b before any reindexing. The finite union of actual truncation supports permits the sum exchange. "
                    + "This theorem is the frequency-one case; it does not assert the general frequency-r opposite insertion or any descendant BPZ or Hermitian adjoint law."))), DescribeRole.Theorem))));
}
