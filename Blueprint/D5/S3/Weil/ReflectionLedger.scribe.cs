using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class ReflectionLedgerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/ReflectionLedger",
            "Conjugate reflection reverses scaling entries around the critical line."),
        H("Conjugate Reflection and Scaling"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("mirror-fixed-points-lie-on-the-critical-line"),
                DescribeKind.Proposition,
                H("Mirror fixed points lie on the critical line"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Conjugate reflection sends a spectral parameter to one minus its conjugate. Every fixed point therefore has real part one half; no zero-location claim is made.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("mirror-reverses-every-scaling-entry"),
                DescribeKind.Theorem,
                H("The mirror reverses every scaling entry"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For the entry given by displacement from one half times ledger length, mirroring negates every coordinate. The same theorem identifies the full fixed locus.")))))));
}
