using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class NormalizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinGProperty/Normalization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero diagonal blocks.",
        H("Zero diagonal blocks"), Blocks(
            Describe.Lean(DescribeId.Create("lin-normalization-0"),
                DeclarationHandle.Create(Owner + "offDiagonal_eq_zero"),
                H("Zero diagonal blocks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("If a positive semidefinite matrix has blocks A, X, X-adjoint and B and either diagonal block vanishes, then X vanishes. Each cross entry has squared modulus bounded by the product of its two diagonal entries."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lin-normalization-1"),
                DeclarationHandle.Create(Owner + "positive_trace"),
                H("Positive trace of a nonzero positive matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("A nonzero positive semidefinite complex matrix has strictly positive real trace. Zero trace would force every eigenvalue, and hence the matrix, to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lin-normalization-2"),
                DeclarationHandle.Create(Owner + "phi_posDef"),
                H("Strict positivity after trace augmentation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("For c at least one, trace augmentation sends every nonzero positive semidefinite matrix to a positive definite matrix. Its scalar identity term has strictly positive coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lin-normalization-3"),
                DeclarationHandle.Create(Owner + "phi_smul"),
                H("Homogeneity of trace augmentation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("Real scaling commutes with the map T to T+c trace(T) I."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lin-normalization-4"),
                DeclarationHandle.Create(Owner + "block_scale_posSemidef"),
                H("Block congruence normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("Congruence by the block diagonal matrix with entries rI and sI preserves positivity and replaces A, X and B by r squared A, rs X and s squared B. Choosing inverse square roots of the diagonal traces normalizes both traces simultaneously."))),
                DescribeRole.Theorem))));
}
