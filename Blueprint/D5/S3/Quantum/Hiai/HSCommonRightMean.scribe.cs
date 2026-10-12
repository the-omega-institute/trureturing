using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class HSCommonRightMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HSCommonRightMean", H("HSCommonRightMean"), Blocks(
            Describe.Lean(DescribeId.Create("lr-pd"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSCommonRightMean.lr_pd"),
                H("Strict positivity of the action product"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("The product of left multiplication by strictly positive X and right multiplication by strictly positive D is strictly positive on the true HS space. Left and right actions commute, even when the original operators do not."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lr-power"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSCommonRightMean.lr_power"),
                H("All real powers of the HS product"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every real s, (L_X R_D)^s = L_(X^s) R_(D^s) on finite nontrivial complex Hilbert space. The full public perspective identity gives the normalized power after cancellation of the invertible right square-root sandwich. Substituting the inverse of D recovers arbitrary powers. Right multiplication reverses products, and every combined right factor here is a power of this same D."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-lr-common"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSCommonRightMean.mean_lr_common"),
                H("Common right factor in the genuine mean"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every real theta, the genuine mean of L_X R_D and L_Y R_D is L_(X #theta Y) R_D. In the normalized middle the right factors D^(-1/2), D, D^(-1/2) cancel; the outer two D^(1/2) factors multiply to D. X and Y may be noncommuting. The triple-variable concavity theorem uses this exact identity."))), DescribeRole.Theorem),
            Paragraph(Text("These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.")))));
}
