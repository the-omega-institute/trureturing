using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NoncommutingClockSublevelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.";

    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded spectral sublevel projections and strict trial-energy bounds for noncommuting positive operator sums.",
        H("Noncommuting clock sublevels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noncommuting-clock-sublevel-projection"),
                DeclarationHandle.Create(Prefix + "sublevelProjection"),
                H("Closed sublevel projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For a bounded self-adjoint operator T on a complex Hilbert space, the closed sublevel projection "
                    + "at ℓ is the orthogonal projection onto the kernel of the positive part of T − ℓ1, formed by continuous functional calculus."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommuting-clock-sublevel-energy"),
                DeclarationHandle.Create(Prefix + "sublevelProjection_energy_lower_bound"),
                H("Strict complementary energy and reduction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For T ≥ 0 and ℓ > 0, the kernel of the shifted positive part and its orthogonal complement "
                    + "are both invariant under T. Writing P for the kernel projection gives ℓ‖(1 − P)x‖² ≤ Re ⟪x, Tx⟫, "
                    + "strict whenever the complementary component is nonzero. On the complement this becomes "
                    + "ℓ‖x‖² < Re ⟪x, Tx⟫ for x ≠ 0. The proof uses orthogonality of the positive and negative parts "
                    + "and strict positivity of the square-root norm away from the kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommuting-clock-trial-energy-rank"),
                DeclarationHandle.Create(Prefix + "sublevel_rank_of_trial_energy"),
                H("Trial-energy sublevel mass and strict rank bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For k orthonormal trial vectors u_j and total energy S = ∑_j Re ⟪u_j, Tu_j⟫, "
                    + "the projection mass satisfies k − S/ℓ ≤ ∑_j ‖Pu_j‖². When the range of P is finite-dimensional "
                    + "with rank r < k, Bessel's inequality bounds this mass by r. At least one trial vector has a nonzero "
                    + "complementary component, so summing the strict energy inequality yields ℓ(k − r) < S."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommuting-clock-sublevel-nonempty-rayleigh"),
                DeclarationHandle.Create(Prefix + "sublevel_nonempty_and_rayleigh_rank"),
                H("Nonzero sublevel and Rayleigh rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("If k > 0 and S ≤ kℓ, the closed spectral sublevel is nonzero. "
                    + "For any trial subspace W satisfying Re ⟪v, Tv⟫ ≤ ℓ‖v‖² for every v in W, "
                    + "the sublevel projection is injective on W. A finite-dimensional sublevel therefore bounds the dimension of W from above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommuting-clock-positive-sum"),
                DeclarationHandle.Create(Prefix + "noncommuting_sum_sublevel_rank_bound"),
                H("Sublevel bounds for positive operator sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For any finite operator sum T = ∑_i A_i† E_i A_i with E_i ≥ 0, positivity holds without "
                    + "commutation hypotheses. The trial energy is exactly S = ∑_j∑_i Re ⟪A_i u_j, E_i A_i u_j⟫. "
                    + "The projection mass and deficient-rank energy bounds apply to this sum, giving a bounded-operator result "
                    + "for the clock-domain question of Footnote 18."))),
                DescribeRole.Theorem))));
}
