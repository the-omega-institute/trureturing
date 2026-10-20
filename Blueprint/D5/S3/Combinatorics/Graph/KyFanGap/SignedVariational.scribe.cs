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
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("A finite orthonormal family together with unit signs records a signed spectral witness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-pairing"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signedPairing"),
                H("Signed quadratic pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The pairing sums the signed quadratic forms of the matrix on the orthonormal family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-pairing-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signed_pairing_le_kyFan"),
                H("Pairing bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("A signed orthonormal family gives a pairing bounded by the Ky Fan sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-pairing-attainment"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.exists_signed_pairing_eq_kyFan"),
                H("Attainment by signed eigenvectors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("For a real symmetric matrix and a prefix no larger than its dimension, sorting an orthonormal eigenbasis by absolute eigenvalue and choosing its signs attains the Ky Fan sum."))),
                DescribeRole.Theorem))));
}
