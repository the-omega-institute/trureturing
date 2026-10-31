using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NegativeRankOneStrongGenerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual all-state outer-insertion obstruction for negative rank one.",
        H("Negative Rank-One Outer-Insertion Obstruction"),
        Blocks(
            Paragraph(Text("The actual all-state coefficient map preserves the original integer energy grading. "
                + "The groundCoefficient projection extracts the oscillator-constant coefficient in one charge sector.")),
            Describe.Lean(
                DescribeId.Create("negative-rankone-ground-coefficient-mode-zero"),
                DeclarationHandle.Create(Prefix + "groundCoefficient_mode_eq_zero_of_grade_mismatch"),
                H("Ground coefficient vanishes under an exact grade mismatch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For arbitrary actual states, arbitrary oscillator mixtures, and arbitrary finite charge support, actual_mode_grade forces the fixed charge/constant coefficient to vanish whenever its target energy differs from the mode grade."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-rankone-outer-energy-mismatch"),
                DeclarationHandle.Create(Prefix + "negative_rank_one_outer_energy_mismatch"),
                H("Negative rank-one outer energy mismatch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For d>0, positive charges s<q, nonnegative oscillator degrees r,t, and a strictly negative mode k, the equality required for a nonzero oscillator-constant output is impossible: r+t+2*d*s*(q-s)-k-1 is strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-rankone-outer-insertion-zero"),
                DeclarationHandle.Create(Prefix + "negative_rank_one_outer_insertion_zero"),
                H("Actual all-state outer insertion vanishes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("Combining the exact actual grading with the arithmetic obstruction gives the single-insertion vanishing used by the bounded-charge projection argument. This increment does not assert the unproved arbitrary-word reordering closure."))),
                DescribeRole.Theorem))));
}
