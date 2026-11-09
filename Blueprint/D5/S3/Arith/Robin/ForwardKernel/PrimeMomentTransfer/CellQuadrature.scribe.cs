using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class CellQuadratureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded variation quadrature for integer floor sampling.",
        H("Cell quadrature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cell-quadrature"),
                DeclarationHandle.Create(Prefix + "cell_quadrature"),
                H("Weighted quadrature with endpoint cells"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let N be at least two and A be nonnegative. Suppose the absolute value of F(n) is at most A for integers from floor(N) through ceil(2N). Let w vanish outside [1,2], with its supremum bound plus total variation at most B. The integral of w(x/N) F(floor(x)) over [N,2N] differs from the sum of w(n/N) F(n) over N<n<=2N by at most 3 A B. Fractional endpoint cells and the shift between left cells and right endpoint sums are included, and values of w at integer sample points are retained."))),
                DescribeRole.Theorem))));
}
