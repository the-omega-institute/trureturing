using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class RealPositiveTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HilbertOperators/RealPositiveTrace.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive trace is an extended nonnegative quantity defined from the operator by all finite orthonormal test families. The definition chooses no basis or scalar spectrum and permits an infinite value.",
        H("Intrinsic Positive Trace on Real Hilbert Spaces"), Blocks(
            Describe.Lean(DescribeId.Create("realpositivetrace-definition"),
                DeclarationHandle.Create(Prefix + "positiveTrace"), H("Positive Trace"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a bounded real linear operator A, positiveTrace(A) is the supremum, over every natural n and every orthonormal family v indexed by Fin n, of the sum of ofReal(inner(v(j),A(v(j)))). Its intended use is for positive operators. Neither compactness nor summability is required to define this extended value."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("realpositivetrace-diagonal"),
                DeclarationHandle.Create(Prefix + "positive_trace_diagonal"), H("Complete Positive Diagonal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let e be a complete real Hilbert basis of E and let A be a continuous real linear operator on that same carrier. Suppose d(i) is nonnegative and, for every vector x and every index i, the i-th coefficient of A(x) is d(i) times the i-th coefficient of x. Then A is positive and its intrinsic positive trace is the extended sum of ofReal(d(i)). The index type can be empty, finite or infinite, and the trace can be infinite.")),
                    Paragraph(Text("Parseval gives the convergent quadratic-form series for each test vector. Interchanging nonnegative extended sums and applying finite-family Bessel bounds each finite orthonormal trace sum by the diagonal sum. Conversely, every finite selection of the supplied eigenvectors is an admissible test family. Taking the supremum of those finite selections gives the reverse inequality. Thus two complete positive diagonal presentations yield the same value because each equals the same operator-defined supremum.")),
                    Paragraph(Text("This is the standard finite-family construction of positive trace. It supplies the original real boundary heat with an intrinsic operator trace without a complexification, a finite-dimensional algebraic trace, or a scalar sequence used as the definition of trace. The separate identification with singular-value trace class is an additional mathematical statement."))), DescribeRole.Theorem))));
}
