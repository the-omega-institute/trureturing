using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuTwoModeRankTwoAttainedOrientationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact attained orientation minimum on the complex rank-two two-mode CAR orbit.",
        H("Attained rank-two orientation minimum"),
        Blocks(
            Paragraph(Text(
                "The public source writes the physical orientation value as a constant plus two occupation contrasts "
                + "and two within-block crossing costs. The weightedCost form uses the real Clifford coordinates of a rank-two "
                + "projection, while planeCoordinates gives an explicit comparison plane.")),
            Entry("wedge-sixth-zero", "wedge_with_sixth_zero", "Coordinate normalization of a unit Plücker form",
                "A unit Plücker coordinate with all Plücker relations has an orthonormal two-plane representation "
                + "whose first vector has sixth coordinate zero and whose wedge is the original coordinate."),
            Entry("weighted-cost-dominates", "additiveCost_le_weightedCost", "Additive comparison cost",
                "For nonnegative mode weights and an orthonormal pair, additiveCost is at most weightedCost of its wedge."),
            Entry("wedge-reduction", "wedge_reduction", "Comparison plane with signed occupations",
                "Every unit Plücker form satisfying the Plücker relations admits X₁, X₂, c₁, c₂ with "
                + "nonnegative masses, X₁+X₂=1, c₁²+c₂²≤1, the two signed coordinates preserved, "
                + "and scalar comparison cost no greater than the original weightedCost."),
            Entry("rank-two-plane-reduction", "rank_two_plane_reduction", "Reduction of a physical projection",
                "For a Hermitian idempotent rank-two matrix and nonnegative mode weights, there is a comparison plane "
                + "with the same two occupation contrasts and with scalar cost bounded by twice the physical crossing cost."),
            Entry("plane-projection-witness", "planeProjection_spec", "Explicit comparison projection",
                "The planeProjection built from admissible X₁, X₂, c₁, c₂ is Hermitian, idempotent, and rank two. "
                + "Its occupation contrasts are the prescribed square-root products, and its two crossing costs are "
                + "X₁+c₁² and X₂+c₂² after the factor of two in the declaration."),
            Entry("orientation-lower-bound", "rank_two_orientation_lower", "Scalar lower bound for every orientation",
                "For every complex rank-two orthogonal projection, orientationValue is bounded below by "
                + "twoModeMinimum with the absolute field magnitudes |B₁| and |B₂|."),
            Entry("axis-witness", "axisProjection_spec", "Single-mode axis projection",
                "For either mode and any z with z²≤1, axisProjection is Hermitian, idempotent, rank two, "
                + "has contrast z in the chosen mode and zero in the spectator mode, with the stated crossing costs."),
            Entry("axis-value", "orientationValue_axisProjection", "Axis value equals scalar quadratic",
                "Choosing favorableContrast for the signed field makes the orientationValue of an axis projection equal "
                + "to the corresponding axisQuadratic with the absolute field magnitude."),
            Entry("minimizing-witness", "minimizingProjection_spec", "Explicit minimizing projection",
                "With nonnegative A₁ and A₂, minimizingProjection is Hermitian, idempotent, and rank two. "
                + "It has zero spectator contrast and zero spectator crossing cost, and its orientationValue equals "
                + "twoModeMinimum with |B₁| and |B₂|."),
            Entry("exact-minimum", "rank_two_orientation_exact_minimum", "Attained exact minimum",
                "The set of values attained by Hermitian idempotent rank-two matrices has least element "
                + "twoModeMinimum C A₁ A₂ |B₁| |B₂|. The witness is minimizingProjection, and the lower-bound "
                + "direction is rank_two_orientation_lower."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
