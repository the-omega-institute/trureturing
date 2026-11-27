using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondSchwinger4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral normalization of the logarithmic series and the exact modified Bessel kernel.",
        H("Integral normalization of the null-diamond correction"),
        Blocks(
            Paragraph(Text("The Schwinger integral determines the logarithmic power series in the four-dimensional "
                + "scalar covariance problem of Satishchandran and Sorce. Its endpoint data fix the solution of "
                + "the differential equation. Hyperbolic substitutions then give the modified Bessel expression.")),
            Entry("schwinger-integral", "schwingerH", "Schwinger integral",
                "For real t, H(t) is the integral of exp(−s−t/s) with respect to Lebesgue measure over s > 0.",
                DescribeRole.Definition),
            Entry("integral-equals-series", "schwingerH_eq_series", "Independently normalized power series",
                "For every real t > 0, H(t), viewed in ℂ, equals 1 + t(log(t) P(t) − B(t)). "
                + "Differentiation under the integral and integration by parts give t H″(t) = H(t). "
                + "Domination by exp(−s) gives the right limit H(0+) = 1. The substitution s = √t exp(r) "
                + "makes the first inverse-power moment twice its tail from √t to infinity. "
                + "Replacing exp(−t/s) by 1 in this tail changes it by at most √t. The tail of exp(−s)/s "
                + "from d to infinity plus log(d) tends to −γ as d decreases to zero, by integration by "
                + "parts and the logarithmic integral for the Euler–Mascheroni constant. "
                + "With d = √t, this gives H′(t) − log(t) tending to 2γ. "
                + "Recurrence of the power-series coefficients gives the same equation and endpoint data. "
                + "For the difference, a mean-value estimate gives uniqueness near zero, and ordinary "
                + "differential equation uniqueness extends the equality to every positive argument."),
            Entry("correction-equals-bessel", "correction_eq_besselK", "Exact modified Bessel correction",
                "For real M, u and v positive and real x < 1, put z = M√(2uv(1−x)). The correction "
                + "equals M²/(16π²) times (z K₁(z) − 2 K₀(z)), embedded in ℂ. "
                + "Here Kν(z) is the integral of exp(−z cosh(s)) cosh(νs) over s > 0. "
                + "The positive-axis hyperbolic integral identities identify H with z K₁(z) and H′ with −2 K₀(z) "
                + "when z = 2√t."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
