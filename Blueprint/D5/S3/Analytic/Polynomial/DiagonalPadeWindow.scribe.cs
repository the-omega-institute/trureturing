using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class DiagonalPadeWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/DiagonalPadeWindow.";
    private static readonly LibraryNoteRef Scardino =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/scardino2026pade");
    private static readonly LibraryNoteRef ThetaTransformation =
        LibraryNoteRef.Create("D5/L/Asymptotics/dlmf2010thetatransformation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal of the normalized diagonal exponential Padé denominator has strictly "
        + "positive rational coefficients throughout the closed quadratic window at all "
        + "sufficiently large odd orders.",
        H("Strict positivity in the odd diagonal Padé window"),
        Blocks(
            Node("theta_real_lower_bound", "Uniform theta lower bound",
                "For any c>0 put C=π²c²/(2(1+c²)²). For every τ in [1/4,1/2] and every real phase "
                + "θ the real part of the sum over integers j of exp(−Cτj²+ijθ) is at least "
                + "sqrt(2π/C) exp(−π²/C)>0. The Gaussian Poisson identity gives a positive "
                + "periodized sum. The integer nearest to θ/(2π) supplies the lower bound.",
                ThetaTransformation),
            Node("exists_uniform_reciprocalCoefficient_pos", "Eventual strict rational positivity",
                "There exists a natural threshold M such that for all odd natural m≥M and natural "
                + "n with 1/4≤n/(m+1/2)²≤1/2, the native rational reciprocal coefficient is "
                + "strictly positive. The central comparison and exterior separation use the same "
                + "inverse, cutoff, reference pole and positive weight. On a fixed finite set "
                + "the Gaussian comparison error decreases with m, and the central modulus "
                + "bound controls the remaining lattice indices by a summable Gaussian. The "
                + "exterior poles have a uniform logarithmic gap. The four errors, including "
                + "the omitted theta terms, total at most half the uniform theta lower bound. "
                + "The exact coefficient identity and the positive normalization transfer this "
                + "estimate to the rational formal reciprocal.", Scardino))));

    private static DocumentBlock Node(string name, string title, string prose, LibraryNoteRef source) =>
        Describe.Lean(
            DescribeId.Create("diagonal-pade-window-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
