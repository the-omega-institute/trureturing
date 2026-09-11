using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class RecordSymmetryNoGoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivariant Hermitian idempotents are trivial under irreducible symmetry.",
        H("Equivariant Record Symmetry No-Go"),
        Blocks(
            Describe.Lean(DescribeId.Create("equivariant-hermitian-idempotents-are-zero-or-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/RecordSymmetryNoGo.equivariant_selfAdjoint_idempotent_eq_zero_or_one"),
                H("Idempotent no-go"),
                StatementSource.FromAuthor(In(F.Id("equivariantIdempotentZeroOrOne"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Schur scalarity followed by the scalar equation r squared equals r gives the two values."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("a-nontrivial-equivariant-idempotent-forces-reducibility"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/RecordSymmetryNoGo.nontrivial_equivariant_selfAdjoint_idempotent_implies_reducible"),
                H("Reverse obstruction"),
                StatementSource.FromAuthor(In(F.Id("nontrivialIdempotentImpliesReducible"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the contrapositive of the idempotent no-go."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-nonzero-orthogonal-records-force-reducibility"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/RecordSymmetryNoGo.two_nonzero_orthogonal_equivariant_records_imply_reducible"),
                H("Two-record consequence"),
                StatementSource.FromAuthor(In(F.Id("twoRecordsImplyReducible"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first projection must be identity under irreducibility, and orthogonality then kills the second."))),
                DescribeRole.Theorem))));
}
