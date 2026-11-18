using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMMetricAdjointOrderObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every faithful nonflat finite complex density, a rotated projective measurement "
        + "has an attainable Gibbs curve that obstructs positive recovery under local operator order.",
        H("Local order for the BKM metric adjoint"),
        Blocks(
            Entry("logarithmic-mean-integral", "omega", "Logarithmic-mean integral",
                "For a reference a and a matrix X, integrate a^u X a^(1−u) over the unit "
                + "interval using the actual real spectral powers.", DescribeRole.Definition),
            Entry("measurement-adjoint", "measurementAdjoint", "Adjoint of the encoded measurement",
                "The complex linear map takes the diagonal part of an output matrix "
                + "and conjugates it by the unitary whose columns define the measurement basis.",
                DescribeRole.Definition),
            Entry("gibbs", "gibbs", "Gibbs exponential",
                "For input reference a, output reference τ and measurement basis V, take "
                + "the matrix exponential of log a plus the measurement adjoint of log Y minus log τ.",
                DescribeRole.Definition),
            Entry("measurement-order-obstruction", "measurement_order_obstruction",
                "Attainable local order obstruction",
                "Choose an unequal eigenpair α>β>0 of a and apply a two-coordinate Hadamard "
                + "rotation in its actual spectral basis. The resulting projective measurement "
                + "with standard diagonal encoding is completely positive and trace preserving. "
                + "Conjugation of the output by V gives the Lüders measurement. Its faithful "
                + "output reference is τ. On all complex matrices the BKM metric adjoint E is "
                + "the logarithmic-mean integral composed with the measurement adjoint and the "
                + "resolvent logarithmic derivative. The spectral coefficients cancel in the "
                + "metric pairing, including the equal-eigenvalue branch. The map E preserves "
                + "trace and adjoints and sends τ to a. For the first selected output projection P, "
                + "the quadratic form of E(P) on the specified vector is strictly negative. "
                + "The line τ+t(P−τ) comes from faithful trace-one inputs near a on both sides "
                + "of zero. The full matrix exponential derivative gives the Gibbs derivative "
                + "E(P)−a. Local positive-semidefinite domination by a positive complex linear "
                + "map R with R(τ)=a would give a scalar local minimum in the same vector, "
                + "forcing the negative quadratic value on R(P). The conclusion concerns this "
                + "additional two-sided order requirement. Trace preservation of R is unnecessary.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
