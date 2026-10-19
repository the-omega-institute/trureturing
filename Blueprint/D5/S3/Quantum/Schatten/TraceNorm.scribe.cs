using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class TraceNormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/TraceNorm";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/hayajneh2018uinorm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The trace norm supplies a unitarily invariant norm in every finite complex dimension, "
        + "with an exact determinant formula in dimension two.",
        H("The trace norm and its two-dimensional formula"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("trace-norm-unitarily-invariant-norm"),
                DeclarationHandle.Create(Module + ".traceNormUINorm"),
                H("The trace norm as a unitarily invariant norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural dimension n, the norm value of a complex "
                    + "n by n matrix A is Re Tr sqrt(A* A). The construction supplies nonnegativity, "
                    + "vanishing exactly at zero, the triangle inequality, complex absolute "
                    + "homogeneity and invariance under left and right unitary multiplication. "
                    + "The existing finite trace-distance laws supply the triangle inequality "
                    + "and a variational formula over unitary matrices. Cyclicity of the trace "
                    + "and multiplication by inverse unitaries establish two-sided unitary "
                    + "invariance. The empty dimension is included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-norm-absolute-determinant"),
                DeclarationHandle.Create(Module + ".det_transitionAbs"),
                H("The determinant of the positive absolute value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every complex two by two matrix T, "
                    + "det sqrt(T* T) is the complex embedding of the nonnegative real number "
                    + "|det T|. Positivity of the Gram matrix allows the determinant to pass "
                    + "through its positive square root. Multiplicativity of the determinant "
                    + "and the adjoint determinant formula identify the resulting square root "
                    + "with |det T|. No invertibility or Hermitian assumption on T is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-norm-two-dimensional-square"),
                DeclarationHandle.Create(Module + ".transitionMass_sq"),
                H("The square of the trace norm in dimension two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every complex two by two matrix T, "
                    + "(Re Tr sqrt(T* T))² equals frobSq(T)+2|det T|, where "
                    + "frobSq(T)=Re Tr(T* T) is its squared Frobenius norm. The two-dimensional "
                    + "trace-power identity applied to sqrt(T* T), together with its real trace, "
                    + "its square T* T and the absolute-determinant formula, proves the equality. "
                    + "The formula applies equally to non-Hermitian and singular matrices, "
                    + "and gives exact rational comparisons for the mixed-power counterexample."))),
                DescribeRole.Theorem))));
}
