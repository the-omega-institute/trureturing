using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Diversity;

internal sealed class SimplexQuadraticOptimalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Diversity/SimplexQuadraticOptimality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/mazhang2026bouafianegativetype");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimizers of a symmetric quadratic form on the probability simplex satisfy the "
            + "support and lower conditions, which characterize them when the form is "
            + "nonnegative on vectors of coordinate sum zero.",
        H("Optimality of a quadratic form on the probability simplex"),
        Blocks(
            Describe.Lean(DescribeId.Create("simplex-quadratic-optimality-energy"),
                DeclarationHandle.Create(Prefix + "energy"),
                H("The quadratic energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a real square matrix Z indexed by a finite set and a real vector p, "
                    + "energy(Z,p) is the quadratic form E(p) = p·(Zp) = Σ_i Σ_j p_i Z_ij p_j. "
                    + "Prob(p) says that every coordinate of p is nonnegative and the "
                    + "coordinates sum to 1, so Prob describes the probability simplex."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("simplex-quadratic-optimality-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The optimality criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let Z be symmetric and p a probability vector. If p minimizes E over "
                        + "the probability vectors, then (Zp)_i = E(p) whenever p_i > 0 and "
                        + "(Zp)_j ≥ E(p) for every j. If moreover E(v) ≥ 0 for every v whose "
                        + "coordinates sum to 0, then these two conditions are equivalent to "
                        + "p minimizing E. A symmetric positive definite Z satisfies the extra "
                        + "hypothesis, which gives Proposition 2 of H. Ma and W. Zhang (version "
                        + "2); it is the first-order condition for a quadratic program on the "
                        + "simplex and recovers Proposition 3 of P. Bouafia in the finite "
                        + "positive-definite setting.")),
                    Paragraph(Text(
                        "For symmetric Z, E(p+td) = E(p) + 2t d·(Zp) + t²E(d). If p is a "
                        + "minimizer and p+td stays a probability vector for all small t > 0, "
                        + "the coefficient d·(Zp) is nonnegative. The direction e_j − p is "
                        + "feasible for t ≤ 1 and gives (Zp)_j ≥ E(p); when p_i > 0 the "
                        + "direction p − e_i is feasible for t ≤ p_i and gives (Zp)_i ≤ E(p). "
                        + "Conversely, for another probability vector q put d = q − p, whose "
                        + "coordinates sum to 0. Then d·(Zp) = Σ_j q_j (Zp)_j − E(p) ≥ 0 by the "
                        + "lower condition and E(d) ≥ 0 by hypothesis, so E(q) ≥ E(p).")),
                    Paragraph(Text(
                        "The hypotheses are needed as follows. Necessity uses only symmetry. "
                        + "For sufficiency the nonnegativity of E on vectors of sum zero cannot "
                        + "be dropped: for Z with zero diagonal and off-diagonal entries 1 on two "
                        + "points, p = (1/2, 1/2) satisfies both conditions with E(p) = 1/2, "
                        + "while the vertices have energy 0. Symmetry is needed in both directions: for "
                        + "Z with rows (0,1) and (−1,0), E vanishes identically, so every "
                        + "probability vector minimizes E, yet at p = (1,0) the second coordinate "
                        + "of Zp is −1 < 0; for Z with rows (0,−2) and (1,0), E(v) = v_1² ≥ 0 on "
                        + "vectors of sum zero and p = (1,0) satisfies both conditions, yet "
                        + "E(1/2,1/2) = −1/4 < 0. These examples are not compiled."))),
                DescribeRole.Theorem))));
}
