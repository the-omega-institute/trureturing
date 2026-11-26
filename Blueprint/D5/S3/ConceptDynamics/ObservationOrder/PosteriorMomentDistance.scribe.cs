using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class PosteriorMomentDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-orbit posterior mixture attains the exact squared Frobenius distance at a fixed uniform prior.",
        H("Distance to a realizable five-target posterior moment"),
        Blocks(
            Definition("five-cycle-input-moment", "cycleMoment", "Five-cycle input family",
                "For every real t, the matrix on Fin 5 has diagonal entries 1/5 − 2t, "
                + "entries t on adjacent pairs modulo five, and zero entries on distinct nonadjacent pairs."),
            Definition("five-cycle-projected-moment", "projectedMoment", "Projected moment",
                "For every real t, put delta = 20t − 1. The matrix on Fin 5 has diagonal entries "
                + "1/10 − delta/15, edge entries 1/20, and distinct nonedge entries delta/30."),
            Definition("posterior-squared-distance", "squaredDistance", "Squared Frobenius distance",
                "For two real matrices on Fin 5, sum the squared differences over all 25 ordered entries."),
            Definition("uniform-finite-posterior-moment", "IsUniformPosteriorMoment", "Finite moment at the uniform prior",
                "A real matrix on Fin 5 is a finite mixture of outer products of probability vectors. "
                + "The mixture masses are nonnegative and sum to one. Its weighted vector mean is "
                + "1/5 at each of the five coordinates."),
            Describe.Lean(
                DescribeId.Create("unique-fixed-prior-posterior-projection"),
                DeclarationHandle.Create(Prefix + "projected_moment_unique"),
                H("Exact distance and unique minimizer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real t with 1/20 ≤ t ≤ 11/160, the projected moment is feasible at "
                        + "the uniform prior, and its squared Frobenius distance to the cycle input equals "
                        + "(20t − 1)²/24. Every finite posterior moment at that prior has squared distance "
                        + "at least this value. Equality implies that the moment is the projected matrix.")),
                    Paragraph(Text(
                        "Average the outer products of the five cyclic shifts of (1/2, 1/2, 0, 0, 0) "
                        + "and of (1/4, 1/2, 1/4, 0, 0). Give the second orbit mass 8(20t − 1)/3 "
                        + "and the first orbit the complementary mass. Each orbit has uniform mean, "
                        + "and their weighted outer products give the projected entries.")),
                    Paragraph(Text(
                        "The five-cycle edge-product sum of any probability vector is at most 1/4, "
                        + "the five-cycle case of Motzkin–Straus, Section 1, Theorem 1. Averaging gives "
                        + "a supporting inequality on moments with arbitrary nonedge entries. The input-to-projection "
                        + "difference is parallel to its normal. The squared-distance expansion leaves a "
                        + "nonnegative cross term and the squared distance to the projected matrix, "
                        + "which gives the minimum and uniqueness."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string declaration, string title, string statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))),
            DescribeRole.Definition);
}
