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
                    + "removes precisely the translated window cuts."))), DescribeRole.Definition))));
}
