using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class OffLineScalingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Off-line nonempty ledger entries share a sign and grow unbounded under scaling.",
        H("Off-Line Scaling Ledger Growth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("off-line-nonempty-ledgers-have-one-sign-and-unbounded-multiples"),
                DeclarationHandle.Create("D5/S3/Midline/OffLineScaling.off_line_scaling_ledger_growth"),
                H("Off-line nonempty ledgers have one sign and unbounded multiples"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("A"), Esc, OpenBracket, Operatorname, Grp(F.Id("AddMonoid")), Open, F.Id("A"), Close, CloseBracket, Comma, Esc, Forall, Sp, Ell, Colon, F.Id("A"), To, Underscore, Grp(Plus), Mathbb, Grp(F.Id("R")), Comma, Esc, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Re, Open, F.Id("s"), Close, Neq, Frac, Grp(D(1)), Grp(D(2)), Esc, Rightarrow, Esc, Open, Forall, Sp, F.Id("a"), InMacro, Sp, F.Id("A"), Comma, Esc, D(0), Lt, Ell, Open, F.Id("a"), Close, Rightarrow, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Neq, Sp, D(0), Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("a"), Comma, F.Id("b"), InMacro, Sp, F.Id("A"), Comma, Esc, D(0), Lt, Ell, Open, F.Id("a"), Close, Rightarrow, Sp, D(0), Lt, Ell, Open, F.Id("b"), Close, Rightarrow, Sp, Open, D(0), Lt, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Leftrightarrow, Sp, D(0), Lt, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("b"), Close, Close, Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("a"), InMacro, Sp, F.Id("A"), Comma, Esc, Forall, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("m"), Cdot, Sp, F.Id("a"), Close, Eq, F.Id("m"), Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("a"), InMacro, Sp, F.Id("A"), Comma, Esc, D(0), Lt, Ell, Open, F.Id("a"), Close, Rightarrow, Forall, Sp, F.Id("C"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc, Exists, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("C"), Lt, Lvert, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("m"), Cdot, Sp, F.Id("a"), Close, Rvert, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For an additive ledger length and a spectral parameter off the critical "
                                    + "line, every positive-length entry is nonzero, any two positive-length "
                                    + "entries have the same sign, natural scaling multiplies each entry by the "
                                    + "same natural number, and the absolute values along those multiples are "
                                    + "unbounded. This is a coordinatewise fact only, not a claim about the sum "
                                    + "after analytic continuation; cancellation of that sum is treated "
                                    + "separately."))),
                DescribeRole.Theorem
            )),
[
                                DocumentEdge.Dependency.Create(
                                    GidRef.Create("D5/S3/Zeros/ZeroGeometry")),
                            ]));
}
