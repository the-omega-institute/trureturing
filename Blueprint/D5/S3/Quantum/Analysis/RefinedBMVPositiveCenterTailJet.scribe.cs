using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVPositiveCenterTailJetDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed derivative for separated refined BMV spectra",
        H("Strict mixed derivative signs for separated refined BMV spectra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-separated-gap"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterTailJet.logKernel_separatedGap_mixed_lt"),
                H("Strict negativity for a gap of at least six"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every first degree at least eleven, the original normalized kernel has a strictly negative mixed " +
                    "derivative when the lower logarithmic coordinate is positive and at most four and the gap is at least six. " +
                    "The leading square and the two linear terms give a positive lower partial and a negative mixed partial " +
                    "before upper normalization. The upper normalization preserves the mixed sign. The normalized radical term " +
                    "has a strictly negative mixed derivative on the same region. This supplies the separated strip of the " +
                    "finite-sample criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-upper-tail"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterTailJet.logKernel_upperTail_mixed_lt"),
                H("Strict negativity for a gap above eleven"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every first degree at least eleven and every positive lower logarithmic coordinate, a gap above " +
                    "eleven gives a strictly negative mixed derivative. Uniform derivative bounds on the linear and radical " +
                    "corrections let the leading square control the sign throughout this region."))),
                DescribeRole.Theorem))));
}
