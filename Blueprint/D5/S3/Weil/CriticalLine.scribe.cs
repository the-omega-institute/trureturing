using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class CriticalLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/CriticalLine",
            "Half-density unitarity characterizes the critical line on a nontrivial ledger."),
        H("Half-Density Unitarity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("half-density-unitarity-characterizes-the-critical-line"),
                H("Half-density unitarity characterizes the critical line"),
                LeanTheorem("D5/S3/Weil/CriticalLine.unitarity_line_iff"),
                Disp(Seq(Forall, Sp, F.Id("A"), Esc, OpenBracket, Operatorname, Grp(F.Id("AddMonoid")), Open, F.Id("A"), Close, CloseBracket, Comma, Esc, Forall, Sp, Ell, Colon, F.Id("A"), To, Underscore, Grp(Plus), Mathbb, Grp(F.Id("R")), Comma, Esc, Open, Exists, Sp, F.Id("a"), Comma, Ell, Open, F.Id("a"), Close, Neq, Sp, D(0), Close, Sp, Rightarrow, Sp, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Open, Open, Forall, Sp, F.Id("a"), Comma, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Eq, D(0), Close, Sp, Leftrightarrow, Sp, Open, Forall, Sp, F.Id("a"), Comma, Vert, Operatorname, Grp(F.Id("halfDensityReading")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Vert, Eq, D(1), Close, Close, Sp, Land, Sp, Open, Open, Forall, Sp, F.Id("a"), Comma, Vert, Operatorname, Grp(F.Id("halfDensityReading")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Vert, Eq, D(1), Close, Sp, Leftrightarrow, Sp, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For an additive ledger with at least one nonzero length coordinate, every scaling entry vanishes exactly when every half-density-normalized reading has norm one, and both conditions hold exactly at real part one half. The nontriviality hypothesis replaces the source ledger's concrete prime-coordinate witness; the statement makes no claim about zeta zeros.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("unitary-weight-is-not-a-zero-proof"),
                H("Unitary weight is not a zero proof"),
                DescribeStatement.FromLean(LeanTheorem("D5/S3/Weil/CriticalLine.unitarity_line_iff")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Half-density normalization singles out the critical line as the norm-preserving weight. It does not prove that a Mellin or Fourier cancellation occurs only at that weight, and spectral-dark-point interpretations remain external to this theorem.")))
            ))));
}
