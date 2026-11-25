using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.NearScalar;

internal sealed class RefinedBMVNearScalarWordMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-copy refined BMV product bound near the identity",
        H("The four-copy refined BMV product bound near the identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-near-scalar-four-copy-product"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/WordMean.wordMean_sub_balanced_ge"),
            H("Quantitative product trace comparison"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "Let p be any natural number, H Hermitian and B positive semidefinite in any finite complex dimension. " +
                "Set A = exp H. If p ‖H‖op ≤ 1/100000, the mean of the real parts of the unnormalized traces " +
                "of all ordered words with p copies of A and four of B is at least the real part of " +
                "Tr((A^(p/4) B)^4) plus p² ‖B(HB − BH)‖F² / 25. The power p/4 is real, and ‖·‖op and ‖·‖F " +
                "are the operator and Frobenius norms. For p > 0 the sufficient radius for ‖H‖op is 1/(100000 p), independent of " +
                "matrix size. This gives a proved neighborhood of the identity for Hägele’s product lower " +
                "comparison (arXiv:2611.00129)."))),
            DescribeRole.Theorem))));
}
