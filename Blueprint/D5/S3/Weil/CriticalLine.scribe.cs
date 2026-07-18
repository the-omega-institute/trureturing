using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class CriticalLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/CriticalLine",
            "Half-density unitarity characterizes the critical line on a nontrivial ledger."),
        H("Half-Density Unitarity"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("half-density-unitarity-characterizes-the-critical-line"),
                DescribeKind.Theorem,
                H("Half-density unitarity characterizes the critical line"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/CriticalLine.unitarity_line_iff")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For an additive ledger with at least one nonzero length coordinate, every scaling entry vanishes exactly when every half-density-normalized reading has norm one, and both conditions hold exactly at real part one half. The nontriviality hypothesis replaces the source ledger's concrete prime-coordinate witness; the statement makes no claim about zeta zeros.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("unitary-weight-is-not-a-zero-proof"),
                DescribeKind.Remark,
                H("Unitary weight is not a zero proof"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/CriticalLine.unitarity_line_iff")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Half-density normalization singles out the critical line as the norm-preserving weight. It does not prove that a Mellin or Fourier cancellation occurs only at that weight, and spectral-dark-point interpretations remain external to this theorem.")))))));
}
