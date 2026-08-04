using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class OffLineScalingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/OffLineScaling",
            "Off-line nonempty ledger entries share a sign and grow unbounded under scaling."),
        H("Off-Line Scaling Ledger Growth"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("off-line-nonempty-ledgers-have-one-sign-and-unbounded-multiples"),
                H("Off-line nonempty ledgers have one sign and unbounded multiples"),
                LeanTheorem(
                    "D5/S3/Midline/OffLineScaling.off_line_scaling_ledger_growth"),
                LatexStatement.Create(
                    @"$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ "
                    + @"\forall s\in\mathbb{C},\ \Re(s)\neq\frac{1}{2}\ \Rightarrow\ "
                    + @"(\forall a\in A,\ 0<\ell(a)\Rightarrow\operatorname{scalingLedger}(\ell,s,a)\neq 0)\ \land\ "
                    + @"(\forall a,b\in A,\ 0<\ell(a)\Rightarrow 0<\ell(b)\Rightarrow "
                    + @"(0<\operatorname{scalingLedger}(\ell,s,a)\Leftrightarrow 0<\operatorname{scalingLedger}(\ell,s,b)))\ \land\ "
                    + @"(\forall a\in A,\ \forall m\in\mathbb{N},\ "
                    + @"\operatorname{scalingLedger}(\ell,s,m\cdot a)=m\operatorname{scalingLedger}(\ell,s,a))\ \land\ "
                    + @"(\forall a\in A,\ 0<\ell(a)\Rightarrow\forall C\in\mathbb{R},\ "
                    + @"\exists m\in\mathbb{N},\ C<\lvert\operatorname{scalingLedger}(\ell,s,m\cdot a)\rvert)$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For an additive ledger length and a spectral parameter off the critical "
                    + "line, every positive-length entry is nonzero, any two positive-length "
                    + "entries have the same sign, natural scaling multiplies each entry by the "
                    + "same natural number, and the absolute values along those multiples are "
                    + "unbounded. This is a coordinatewise fact only, not a claim about the sum "
                    + "after analytic continuation; cancellation of that sum is treated "
                    + "separately.")))))));
}
