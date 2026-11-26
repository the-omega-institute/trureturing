using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVClearedMiddleSignDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV mixed derivative on the middle band",
        H("The refined BMV mixed derivative on the middle band"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-cleared-middle-sign"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleSign.logKernel_mixed_neg_cleared_middle"),
            H("Strict negativity from gaps one through four"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "For every degree at least eleven, the original normalized kernel has strictly " +
                "negative mixed derivative when the lower coordinate belongs to the closed interval " +
                "from one half to four and the gap belongs to the closed interval from one to four. " +
                "Exact Taylor bounds on 39 cells certify the sign uniformly in the degree."))),
            DescribeRole.Theorem))));
}
