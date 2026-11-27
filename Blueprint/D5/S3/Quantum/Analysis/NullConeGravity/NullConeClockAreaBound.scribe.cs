using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullConeClockAreaBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.";

    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Noncommutative operator Cauchy-Schwarz rigidity and shear-focusing clock-area bounds on any complex Hilbert space.",
        H("Noncommutative null-cone clock-area bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("null-cone-clock-operator-cauchy-schwarz-identity"),
                DeclarationHandle.Create(Prefix + "operator_weighted_cauchy_schwarz_identity"),
                H("Exact noncommutative weighted operator Cauchy-Schwarz identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(
                    Paragraph(Text("For any finite index set, real weights w_i, and arbitrary (not necessarily commuting) "
                        + "bounded linear operators A_i on a complex Hilbert space H, the weighted second-moment defect "
                        + "(∑ w_i)(∑ w_i ‖A_i η‖²) − ‖(∑ w_i A_i) η‖² equals half the double sum ∑_i ∑_j w_i w_j ‖(A_i − A_j) η‖².")),
                    Paragraph(Text("Expanding the squared norm of the weighted sum via the complex inner product "
                        + "and comparing against pairwise norm-difference squares yields the identity with no commutativity assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("null-cone-clock-operator-cauchy-schwarz-le"),
                DeclarationHandle.Create(Prefix + "operator_weighted_cauchy_schwarz_le"),
                H("Noncommutative weighted operator Cauchy-Schwarz inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("When all weights w_i are nonnegative, the exact pairwise-difference sum is nonnegative, "
                    + "giving ‖(∑ w_i A_i) η‖² ≤ (∑ w_i)(∑ w_i ‖A_i η‖²)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("null-cone-clock-operator-cauchy-schwarz-eq-iff"),
                DeclarationHandle.Create(Prefix + "operator_weighted_cauchy_schwarz_eq_iff"),
                H("Uniform-cap rigidity for operator Cauchy-Schwarz"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("When all weights w_i are strictly positive, equality holds on η if and only if "
                    + "A_i η = A_j η for every pair i, j in the index set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("null-cone-clock-operator-shear-lower-bound"),
                DeclarationHandle.Create(Prefix + "operator_shear_clock_lower_bound"),
                H("Noncommutative shear-focusing clock lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(
                    Paragraph(Text("Extends the null-cone gravitational clock bound (Chandrasekaran, arXiv:2611.34924v1, Eqs. 4.26–4.27 and 5.21a–c) "
                        + "to arbitrary noncommuting bounded operators A_i with fixed total area ∑ w_i ‖A_i η‖² = area · ‖η‖², "
                        + "self-adjoint square root B with B² = ∑ w_i A_i, and focusing operators E_i satisfying Re ⟪v, E_i v⟫ ≥ ‖v‖².")),
                    Paragraph(Text("Combining focusing monotonicity with the noncommutative operator Cauchy-Schwarz bound on a = ∑ w_i A_i "
                        + "and Hilbert-space Cauchy-Schwarz on ‖B η‖² = Re ⟪η, a η⟫ yields "
                        + "(1 − ε) √(area / M) ‖B η‖² ≤ (1 − ε) ∑ w_i Re ⟪A_i η, E_i(A_i η)⟫ without classical Wigner heuristics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("null-cone-clock-operator-area-upper-bound"),
                DeclarationHandle.Create(Prefix + "operator_clock_area_upper_bound"),
                H("Corner-area ceiling from a bounded noncommutative clock reading"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Whenever B η ≠ 0 and the noncommutative clock quadratic form is at most ℓ ‖B η‖² "
                    + "(ℓ ≥ 0, ε < 1), the fixed corner area obeys area ≤ M ℓ² / (1 − ε)² (generalizing Eq. 5.21d)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("null-cone-clock-classical-def"),
                DeclarationHandle.Create(Prefix + "shearDelayedClock"),
                H("Shear-delayed corner clock reading"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Area-weighted average of per-generator clock readings (1 − ε) ρ_i + δ_i over a finite corner partition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("null-cone-clock-deficit-and-rigidity"),
                DeclarationHandle.Create(Prefix + "shear_clock_deficit_and_rigidity"),
                H("Two-channel clock deficit decomposition and uniform shear-free rigidity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Decomposes the excess of the shear-delayed clock over the round shear-free floor (1 − ε) √(A / M) "
                    + "into two nonnegative channels—corner-density inhomogeneity and radiative shear delay—and proves that equality holds "
                    + "if and only if every shear delay vanishes and the corner density is constant."))),
                DescribeRole.Theorem))));
}
