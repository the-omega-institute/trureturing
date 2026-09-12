using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class ComplexHadamardEntrywiseDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entrywise unit norms are equivalent to a vanishing squared-deviation sum.",
        H("Complex Hadamard Entrywise Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("entrywise-defect-unit-norm-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect."
                    + "entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero"),
                H("Unit entry norms and zero scalar defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a complex matrix with finite row and column types, every entry "
                    + "has squared norm one if and only if the sum over all entries of "
                    + "the square of its squared norm minus one is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entrywise-defect-hadamard-characterization"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect."
                    + "isComplexHadamard_iff_scalarDefect_and_rowGram"),
                H("Hadamard characterization by scalar defect and row Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A complex square matrix on a finite coordinate type with decidable "
                    + "equality is complex Hadamard if and only if its summed squared "
                    + "entry-norm deviations vanish and the matrix times its adjoint "
                    + "equals the coordinate cardinality times the identity."))),
                DescribeRole.Theorem))));
}
