using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitScanExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary actual slot scans extend retained response recipes with exact excess.",
        H("Four-Exit Scan Extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-exit-ordinary-scan-completion"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitScanExtension.ordinary_scan_completion"),
            H("Extension from an arbitrary retained slot set"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Fix any coordinate equivalence for the baseline and the four exceptional rows "
                + "at each slot. A recipe on the baseline and any retained set of slots extends "
                + "to a recipe on the complete family. Its gain is unchanged on every retained "
                + "coordinate and equals one on all four rows of every added slot. "
                + "The assertion includes empty and full retained sets.")),
                Paragraph(Text(
                "The three actual queries at an added slot are LLLR, LRR, and RLR. "
                + "The first separates A and Y; the second separates H; the third separates Z. "
                + "Each exceptional row exits after one nonleaf reply, while every other row "
                + "continues through labelled leaves. Induction over the added slots composes "
                + "these splits with the original retained recipe."))),
            DescribeRole.Theorem))));
}
