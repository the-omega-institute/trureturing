using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMSpectralVarianceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMSpectralVariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eigenbasis formulas and a conditioned variance bound for the finite BKM integral.",
        H("Spectral variance of rank-one BKM outputs"),
        Blocks(
            Entry("unitary-trace", "trace_conjStarAlgAut_symm", "Trace under unitary conjugation",
                "Conjugating a finite complex matrix by a unitary preserves its complex trace.",
                DescribeRole.Theorem),
            Entry("spectral-basis", "fromEigenbasis", "Conjugation from the reference eigenbasis",
                "The eigenvector unitary of a positive definite reference takes a matrix in its "
                + "eigenbasis back to the original coordinates by conjugation.", DescribeRole.Definition),
            Entry("bkm-linearity", "omegaLinear", "Linearity of the BKM integral",
                "For a positive definite reference, the eigenbasis formula expresses the BKM "
                + "integral as multiplication by fixed scalars on entries. This gives a complex-linear "
                + "map on the matrix algebra.", DescribeRole.Definition),
            Entry("hermitian-output", "omega_isHermitian", "Hermitian inputs and outputs",
                "In the reference eigenbasis, the BKM integral multiplies each entry by the real "
                + "logarithmic mean of its two eigenvalues. The symmetry of this multiplier preserves "
                + "the Hermitian relation between transposed entries.", DescribeRole.Theorem),
            Entry("rank-one-trace", "omega_rankOne_trace_re", "First spectral moment",
                "The real trace of the BKM output of a rank-one outer product is the sum of the "
                + "reference eigenvalues weighted by the squared moduli of the vector's "
                + "eigenbasis coordinates.", DescribeRole.Theorem),
            Entry("rank-one-hermitian", "omega_rankOne_isHermitian", "Hermitian rank-one output",
                "A rank-one outer product formed in the reference eigenbasis is Hermitian after "
                + "conjugation, so its BKM output is Hermitian as well.", DescribeRole.Theorem),
            Entry("rank-one-variance", "omega_rankOne_trace_sq_sub_trace_sq_ge",
                "Spectral variance and the trace-square deficit",
                "For a unit vector, its squared coordinate moduli form probability weights. "
                + "If T bounds all absolute log-ratios of the positive reference eigenvalues, "
                + "the real trace of the squared BKM output minus the square of its real trace "
                + "is at least twice the weighted eigenvalue variance divided by 12 + T². "
                + "The estimate follows by summing the scalar logarithmic-mean bound over "
                + "pairs of eigenvalues.", DescribeRole.Theorem),
            Entry("bkm-trace", "omega_trace_eq_trace_mul", "Trace of the BKM integral",
                "For every complex matrix input, the BKM output has the same complex trace as the "
                + "product of the reference and the input. The diagonal logarithmic-mean "
                + "multipliers in the reference eigenbasis are the eigenvalues themselves.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
