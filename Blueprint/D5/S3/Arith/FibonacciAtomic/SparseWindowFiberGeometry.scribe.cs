using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SparseWindowFiberGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The geometry of sparse Fibonacci window labels on the circle.",
        H("Sparse Window Fibres"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sparse-window-fiber-geometry-fiber"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry.fiber"),
                H("Time tuple fibres"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A time tuple fibre is the intersection of the window arcs "
                    + "translated back by their retained observation times. The regular domain "
                    + "removes precisely the translated window cuts."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparse-window-fiber-geometry-components"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry.sparse_window_fiber_geometry"),
                H("Fibres and connected components"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For width at least two and a nonempty finite set of times, "
                    + "every nonempty tuple fibre equals a connected component of the regular domain. "
                    + "A component determines its tuple uniquely, and each regular point has one tuple. "
                    + "The number of distinct circle cuts equals the number of their natural indices. "
                    + "Every nonempty fibre contains a golden phase with natural index above any given bound. "
                    + "The phase visits refer to circle rotation; identification with canonical natural "
                    + "digit rows is an additional relation."))), DescribeRole.Theorem))));
}
