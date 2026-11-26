using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class DiagonalPadeExteriorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/DiagonalPadeExterior.";
    private static readonly LibraryNoteRef SaffVarga =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/saffvarga1976parabolic");
    private static readonly LibraryNoteRef Scardino =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/scardino2026pade");
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Asymptotics/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parabolic exclusion and the corrected phase separate exterior Padé poles from the full central lattice.",
        H("Exterior poles of the diagonal exponential Padé denominator"),
        Blocks(
            Node("denominator_root_norm_add_re", "Parabolic exclusion",
                "Every root ζ of the diagonal exponential Padé denominator of natural order m "
                + "satisfies |ζ| + Re ζ ≥ 2(m+1). Fix the numerator order and vary the denominator "
                + "degree k. The factorial-scaled reflected polynomials satisfy the continuant "
                + "recurrence P_(k+2) = (z+m+k+2)P_(k+1) − (k+1)zP_k. "
                + "In the excluded region their successive ratios have the form z+u with "
                + "Re u ≥ m+1. Completing a square shows that z+u is nonzero and "
                + "Re(z/(z+u)) ≤ 1, which closes the induction. At k=m, the exact "
                + "reversal identifies the reflected polynomial with the native denominator.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SaffVarga)),
            Node("exists_uniform_scaled_exterior_radius", "Uniform separation in scaled radius",
                "Let 0<c<1 be a real zero of the limiting phase η and let ε>0. For all sufficiently "
                + "large odd m, every scaled pole w=ζ/(2ν) outside the open ε-disk about c "
                + "satisfies |w|≥c+δ for one δ>0 independent of m. Parabolic exclusion puts "
                + "the poles with modulus at most a fixed d between c and 1 in a strict "
                + "right half-plane sector. Along a semicircular arc the derivative of "
                + "Re η with respect to angle is −Im sqrt(1+w²). The real-axis phase is "
                + "strictly increasing, so c is the only point of radius at most c in that "
                + "sector with vanishing real phase. Compactness gives a positive lower bound "
                + "for max(|w|−c, |Re η(w)|) away from the disk. At a pole the corrected "
                + "phase is purely imaginary and approximates η uniformly in the sector.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(SaffVarga, Dlmf)),
            Node("exteriorPoles", "Exterior pole set",
                "Filter the distinct denominator roots by excluding every value "
                + "2ν g(j π i/ν) whose phase norm is at most the full central cutoff.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("exists_uniform_exterior_pole_gap", "Uniform logarithmic gap and aggregate estimate",
                "At the positive phase zero 0<c<1, a fixed cutoff, inverse disk, localization disk "
                + "and positive gap work for every sufficiently large odd order. The analytic "
                + "inverse gives distinct roots throughout the full cutoff, including every "
                + "root scaled into the localization disk. The index-zero root r and its "
                + "residue are positive. For every other pole outside the full cutoff "
                + "log(|ζ|/r)≥λ for one λ>0. The reference scaled pole converges to c, "
                + "so the uniform exterior radius bound gives the logarithmic gap. "
                + "For 1/4≤n/ν²≤1/2 the norm of the normalized exterior sum is at most "
                + "m exp(−λν²/4). The native residue bound controls each term and the "
                + "denominator degree bounds their number.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino, Dlmf, SaffVarga)))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role,
        AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("diagonal-pade-exterior-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
