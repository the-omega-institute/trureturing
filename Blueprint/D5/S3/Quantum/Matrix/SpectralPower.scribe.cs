using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SpectralPowerDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/SpectralPower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real spectral powers and Log-Euclidean means of finite complex matrices, "
        + "with elementary power identities and a two-dimensional positivity criterion.",
        H("Spectral powers and matrix positivity"),
        Blocks(
            Entry("matrix-power", "mpow", "Real matrix powers",
                "For a finite complex square matrix X and real p, mpow X p is "
                + "cfc (t ↦ t^p) X. On positive definite matrices this is the usual "
                + "positive real power. The functional calculus is total; this definition "
                + "alone asserts neither positivity nor Hermitian symmetry for arbitrary inputs.",
                DescribeRole.Definition),
            Entry("log-euclidean", "LE", "Log-Euclidean means",
                "LE α A B is cfc exp ((1−α) • cfc log A + α • cfc log B). "
                + "For positive definite A and B this is exp((1−α) log A + α log B). "
                + "The weight α is any real number.", DescribeRole.Definition),
            Entry("power-one", "mpow_one", "The first power",
                "For every Hermitian finite complex matrix X, mpow X 1 = X. "
                + "This is the identity-function law of the continuous functional calculus.",
                DescribeRole.Theorem),
            Entry("power-two", "mpow_two", "The second power",
                "For every Hermitian finite complex matrix X, mpow X 2 = X * X. "
                + "This follows from the polynomial law of the continuous functional calculus.",
                DescribeRole.Theorem),
            Entry("positive-two", "posDef_two", "Positive definite two by two matrices",
                "For real a, b, c, the complex matrix [[a,b],[b,c]] is positive definite "
                + "if a>0 and ac−b²>0. Its factorization U D U* uses "
                + "U=[[1,0],[b/a,1]] and D=diag(a,c−b²/a). The diagonal entries "
                + "are positive and U is invertible. This criterion supplies positivity "
                + "both for Pauli clock matrices and for Wasserstein counterexamples.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
