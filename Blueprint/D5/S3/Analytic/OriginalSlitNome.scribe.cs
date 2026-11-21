using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalSlitNomeDocument : IScribeDocumentDefinition
{
    private const string Analytic = "D5/S3/Analytic/";
    private const string Prefix = Analytic + "OriginalSlitNome.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native nome and rank-24 determinant on the Euler slit",
        H("Holomorphic continuation from the sewing cusp"),
        Blocks(
            D("punctured-slit", "puncturedSlit", "Punctured Euler slit", DescribeRole.Definition,
                Text("Remove the cusp r = 0 from the Euler slit, the domain on which 1 − r "
                    + "lies in the principal slit plane.")),
            D("slit-nome", "slitNome", "The continued lattice nome", DescribeRole.Definition,
                Text("Set the nome to zero at the cusp. Off zero use exp(iπτ(r)) on the double slit "
                    + "and the signed Pfaff nome on the negative real axis. The Pfaff jump identifies "
                    + "the two expressions on the overlap of the local Pfaff chart with the double slit. "),
                Ref(Analytic + "OriginalHalfBinomialPfaffNome.negative_real_nome_extension")),
            D("slit-nome-disk", "slitNome_eq_Q0", "Agreement with the native disk nome", DescribeRole.Theorem,
                Text("On |r| < 1 the continuation equals Q₀(r), including at zero. The identity theorem "
                    + "propagates the equality from the lens around r = 1/2 to the slit disk. "
                    + "Continuity then extends the equality to the negative real points of the disk. "),
                Ref(Analytic + "OriginalHalfBinomialNome.actual_nome_source")),
            D("slit-nome-exponential", "slitNome_eq_exp", "The period-ratio expression", DescribeRole.Theorem,
                Text("At every point of the double slit the glued nome equals exp(iπτ(r)). "
                    + "This is the expression used to compare the nome to a D-lip branch.")),
            D("slit-nome-analytic", "slitNome_analyticOnNhd", "Holomorphy on the Euler slit", DescribeRole.Theorem,
                Text("The double-slit exponential and the signed Pfaff chart are holomorphic at every "
                    + "nonzero point of the Euler slit. At the cusp, equality on the disk transfers "
                    + "holomorphy from Q₀. "),
                Ref(Analytic + "OriginalHalfBinomialNome.actual_nome_disk")),
            D("slit-nome-subunit", "slitNome_norm_lt_one", "Strict unit-disk bound", DescribeRole.Theorem,
                Text("The nome has modulus strictly below one throughout the Euler slit. "
                    + "The exponential has modulus exp(−π Im τ) on the double slit. The Pfaff chart "
                    + "supplies the same strict bound on the negative real axis, and zero covers the cusp.")),
            D("rank24-determinant", "rank24Determinant", "Rank-24 determinant factor", DescribeRole.Definition,
                Text("For the Euler period P, the rank-24 scalar factor is (1 − r)⁻³ P(r)⁻¹². "
                    + "Both powers have integral exponents.")),
            D("rank24-determinant-analytic", "rank24Determinant_analyticOnNhd",
                "Holomorphy of the determinant factor", DescribeRole.Theorem,
                Text("The factor is holomorphic at every point of the Euler slit. The factor 1 − r is "
                    + "nonzero there, and the Euler period is holomorphic and nonzero. "),
                Ref(Analytic + "OriginalHalfBinomialSlitPeriod.slitPeriod_analyticOnNhd"), Text(", "),
                Ref(Analytic + "OriginalHalfBinomialSlitPeriod.slitPeriod_ne_zero")))));

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
