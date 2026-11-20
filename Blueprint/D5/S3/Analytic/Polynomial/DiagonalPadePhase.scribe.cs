using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class DiagonalPadePhaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/DiagonalPadePhase.";
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Analytic/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The corrected analytic phase quantizes the central poles of the odd diagonal Padé denominator.",
        H("Central phase of the diagonal exponential Padé denominator"),
        Blocks(
            Node("exists_eta_positive_zero", "Simple positive zero of the limiting phase",
                "The native Liouville–Green phase has a unique positive real zero c in (0, 1). "
                + "Its complex derivative at c is sqrt(1+c²)/c. On the positive line the phase "
                + "increases strictly, tends to minus infinity at zero, and is positive at one.",
                DescribeRole.Theorem),
            Node("polePhase", "Corrected phase",
                "With ν = m + 1/2, the phase Φ_m is η + Log(F_I/F_K)/(2ν). "
                + "The logarithm is the principal complex logarithm.",
                DescribeRole.Definition),
            Node("polePhase_sector", "Analyticity and sector bound",
                "For 0 < κ ≤ 1 and ν ≥ 40 V_κ/κ, both amplitudes are nonzero in the open sector "
                + "κ |w| < Re w. The ratio has strictly positive real part and the phase is "
                + "analytic there. The phase differs from η by at most 15 V_κ/(κν²).",
                DescribeRole.Theorem),
            Node("polePhaseLattice", "Integer phase value",
                "The phase value of index j is j π i/ν.",
                DescribeRole.Definition),
            Node("denominator_zero_iff_polePhase", "Exact odd-order phase lattice",
                "For odd m with the same sector and order conditions, q_m(2ν w) vanishes exactly "
                + "when Φ_m(w) = j π i/ν for an integer j. Exponentiating the corrected phase "
                + "gives π I_m(ν w)/K_m(ν w), whose equality to one is the vanishing condition.",
                DescribeRole.Theorem),
            Node("polePhase_compact_estimate", "Uniform perturbation on nested disks",
                "For positive c and ν ≥ 160 V_(1/4), the phase error is at most 60 V_(1/4)/ν² "
                + "on the closed disk of radius c/2 about c. Its derivative is bounded by "
                + "240 V_(1/4)/(cν²) on the closed disk of radius c/4. The larger disk lies "
                + "inside the open sector and a circle of radius c/4 about each point of the "
                + "smaller disk gives the Cauchy estimate.",
                DescribeRole.Theorem),
            Node("exists_uniform_polePhase_inverse", "Uniform inverse on a fixed disk",
                "At a positive real zero c of η, there are fixed positive radii r ≤ c/4 and ρ "
                + "and a constant B > 0. For all sufficiently large orders, with threshold at "
                + "least 160 V_(1/4) in ν, η and Φ_m have analytic inverses g and g_m on the "
                + "open disk of radius ρ about zero. Their values lie in the open disk of radius "
                + "r about c, and each is the unique solution in the corresponding closed disk. "
                + "Throughout the inverse disk, |g_m-g| ≤ B/ν². A uniform affine derivative "
                + "estimate gives a contraction on the closed disk and the local inverse "
                + "theorem establishes analyticity.",
                DescribeRole.Theorem),
            Node("norm_polePhaseLattice", "Modulus of a lattice value",
                "The modulus of the phase value at integer index j is |j| π/ν.",
                DescribeRole.Theorem),
            Node("exists_central_poles", "Central poles and uniform estimates",
                "About every positive zero c of η there are fixed radii 0 < ε ≤ r ≤ c/4 "
                + "and 0 < t₀ < ρ, positive constants B and C, and an order threshold. "
                + "Above it, the corrected phase at odd orders has an analytic inverse g_m "
                + "on the open disk of radius ρ. Its values lie in the open disk of radius r "
                + "about c, it commutes with conjugation and its value at zero is positive real "
                + "and within B/ν² of c. For every |j| π/ν ≤ t₀ there is a distinct pole "
                + "at 2ν g_m(j π i/ν). This list includes every root whose scaled argument "
                + "lies in the open disk of radius ε about c. Every fixed finite range of "
                + "integer indices lies within the cutoff for all sufficiently large orders. "
                + "For real |t| ≤ t₀, log(|g_m(it)|/|g_m(0)|) is at least "
                + "c² t²/(4(1+c²)²). The derivative of the limiting log inverse is 1/S(g(s)) "
                + "and its second derivative at zero is −c²/(1+c²)². Cauchy's estimate "
                + "transfers the curvature to the corrected inverse. "
                + "Write a = sqrt(1+c²)/c, b = 1/sqrt(1+c²) and D = c²/(2(1+c²)²). "
                + "For complex |s| ≤ t₀, g_m(s)−g_m(0) differs from s/a by at most "
                + "C(|s|/ν²+|s|²), and Log g_m(s)−Log g_m(0) differs from bs−Ds² by at most "
                + "C(|s|/ν²+|s|³).",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("diagonal-pade-phase-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Dlmf), Blocks(Paragraph(Text(prose))), role);
}
