using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuTwoModeCliffordPlueckerDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Oriented real two-planes give Plücker coordinates for the complex two-mode CAR rank-two cut.",
        H("Clifford and Plücker coordinates for the rank-two cut"),
        Blocks(
            Paragraph(Text("Use the two-mode tracial CAR setting of Wu v1, Remark 3.15. In the ordered " +
                "occupation basis (00, 01, 10, 11), let L = |0⟩⟨1| and Z = diag(1, −1). Mode 0 is the " +
                "right mode with lowering jump J₀ = Z ⊗ L. Mode 1 is the left mode with J₁ = L ⊗ I. " +
                "These are −modeJump 1 and modeJump 0 in the repository, respectively.")),
            Describe.Lean(DescribeId.Create("rank-two-projection-certificate"),
                DeclarationHandle.Create(Owner + "rank_two_projection_certificate"),
                H("Coordinates of a complex rank-two projection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("For a complex Hermitian idempotent P of rank two, the traceless " +
                    "involution K = 2P − I expands in the fifteen Hermitian Clifford letters Bₖ with real " +
                    "coefficients pₖ = coordinates(K)ₖ. The squared norm ∑ₖ pₖ² is one and all fifteen " +
                    "Plücker relations vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("projection-of-coordinates"),
                DeclarationHandle.Create(Owner + "projection_of_coordinates"),
                H("Realizing the coordinates by a projection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("Conversely, every real unit solution p of the Plücker relations " +
                    "gives a complex Hermitian idempotent P = (I + expand(p))/2 of rank two. Its " +
                    "involution is expand(p) = ∑ₖ pₖ Bₖ."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unit-pluecker-iff"),
                DeclarationHandle.Create(Owner + "unit_pluecker_iff"),
                H("Oriented real two-planes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("A real array p has squared norm one and satisfies all the Plücker " +
                    "relations exactly when p = u ∧ v for an ordered orthonormal pair in ℝ⁶. Its entries " +
                    "are the signed two-by-two minors uᵢvⱼ − uⱼvᵢ. Together with the converse projection " +
                    "construction, this realizes every oriented real two-plane as coordinates of a " +
                    "complex rank-two projection."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("within-quadratic"),
                DeclarationHandle.Create(Owner + "within_quadratic"),
                H("Per-mode quadratic cut weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("For either lowering jump Jⱼ, let Wⱼ = Re Tr(P Jⱼ P Jⱼ†) be the " +
                        "weight within the range of P. The theorem gives 2(1 − Wⱼ) = ∑ₖ modeDegree(j,k) pₖ². " +
                        "For the cut between P and I − P, the two directed lowering weights sum to " +
                        "2(1 − Wⱼ), since Jⱼ†Jⱼ + JⱼJⱼ† = I and Tr(P) = 2.")),
                    Paragraph(Text("The signed occupation is Sⱼ = I − 2Jⱼ†Jⱼ, with sign +1 on an empty " +
                        "mode and −1 on an occupied mode. Write qⱼ = Re Tr((2P − I) Sⱼ)/4. It equals " +
                        "coordinate p₀ for the right mode and p₉ for the left mode, the 12 and 34 pairs " +
                        "with one-based vertex labels. The occupied trace Re Tr(P Jⱼ†Jⱼ) is 1 − qⱼ. " +
                        "Subtracting Wⱼ from the occupied and empty traces gives the lowering weights " +
                        "1 − Wⱼ − qⱼ out of P and 1 − Wⱼ + qⱼ into P, respectively."))),
                DescribeRole.Theorem))));
}
