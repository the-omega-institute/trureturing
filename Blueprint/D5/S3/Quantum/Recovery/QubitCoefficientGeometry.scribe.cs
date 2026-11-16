using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class QubitCoefficientGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two physical input columns are split by their output qubit label. Isometry orthogonality relates their retained and flipped vectors, controls the phase-sensitive coefficient cancellation and converts a diagonal residual into quantitative flip bounds.",
        H("Physical qubit coefficient geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("column"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.column"),
                H("The four physical column slices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The output B coordinate splits the two Stinespring columns into retained and flipped vectors in the full environment space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced"),
                H("The reduced physical action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation by the isometry followed by the actual environment partial trace defines the reduced qubit action on every complex input matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("retained-flip-norms"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.retained_flip_norms"),
                H("Retained and flipped column norms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each isometry input column, the squared norms of its retained and flipped output slices sum to one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("retained-gap"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.retained_gap"),
                H("Retained vectors and their phase gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The squared norm of the difference between the retained vectors is at most twice the modulus of one minus their complex inner product."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("isometry-coefficient-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.isometry_coefficient_geometry"),
                H("Phase-sensitive two-column cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite environment and actual two-column isometry, the reduced off-diagonal entry is the sum of four complex coefficient terms. Column orthogonality gives exact cancellation in the sum of the two diagonal-to-coherence coefficients. Their modulus is bounded by twice the square root of total flip probability times the square root of the phase-sensitive retained-column gap. No unitality is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("traceless-qubit-entry-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.traceless_qubit_entry_bounds"),
                H("Entries of a traceless Hermitian qubit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a traceless Hermitian two by two matrix, each diagonal and off-diagonal entry has modulus bounded by half the trace norm."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-residual-controls-coefficients"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.diagonal_residual_controls_coefficients"),
                H("Diagonal residual bounds the flip terms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A trace-norm residual e for the diagonal Pauli direction bounds both the total flip probability and the difference of the diagonal-to-coherence coefficients by e divided by two. The exact trace norm of a traceless Hermitian qubit supplies both bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reduced-hermitian"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced_hermitian"),
                H("Hermiticity of the reduced action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying an isometry on both sides and discarding the environment preserves Hermiticity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reduced-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced_trace"),
                H("Trace of the reduced action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reduced action of an isometry preserves the matrix trace."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("offdiagonal-gap-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.offDiagonal_gap_bound"),
                H("A phase-sensitive coherence bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every traceless Hermitian qubit M tested against the same actual isometry, the retained-column gap times the off-diagonal modulus is bounded by half its trace-norm residual plus the coefficient-difference bound times its operator-norm bound and half the flip bound times that operator-norm bound. Complex phases and both nonunital coherence coefficients are retained."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rotated-dilation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.rotated_dilation"),
                H("Rotate the same physical isometry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A qubit unitary rotates the input and output of a physical isometry together and gives the corresponding conjugated reduced action on every complex matrix."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-dilation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCoefficientGeometry.actual_dilation"),
                H("A dilation of the actual channel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every canonical qubit channel with finite physical output has a finite isometric dilation whose environment partial trace equals the channel on every matrix."))), DescribeRole.Theorem))));
}
