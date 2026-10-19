using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class SignedVariationalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed orthonormal pairings and the Ky Fan variational interface.",
        H("Signed variational interface"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-witness"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.SignedWitness"),
                H("Signed orthonormal witness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("A finite orthonormal family together with unit signs records a signed spectral witness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-involution"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signedInvolution"),
                H("Signed involution predicate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The predicate records symmetry, the cubic involution equation, and the prescribed finite rank."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-pairing-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signed_pairing_le_kyFan_of_one"),
                H("Pairing bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("When all witness signs are positive, the paired real inner product is bounded by the Ky Fan sum."))),
                DescribeRole.Theorem))));
}
