using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class DiagonalPadeCentralPolesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/DiagonalPadeCentralPoles.";
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Asymptotics/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The analytic phase inverse indexes the central poles and controls their radial growth.",
        H("Central poles of the diagonal exponential Padé denominator"),
        Blocks(
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
