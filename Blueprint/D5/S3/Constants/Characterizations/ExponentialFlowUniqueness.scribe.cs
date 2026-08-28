using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Characterizations;

internal sealed class ExponentialFlowUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive normalized multiplicative C1 flow is the real exponential.",
        H("Exponential Flow Uniqueness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exponential-flow-uniqueness"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Characterizations/ExponentialFlowUniqueness."
                        + "exponential_flow_unique"),
                H("The normalized exponential flow is unique"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The strict positivity condition is the real-valued encoding of the "
                            + "source codomain of positive reals. Together with C1 regularity, "
                            + "the multiplicative Cauchy equation, and the derivative value one "
                            + "at zero, it gives exactly the hypotheses of the formal theorem.")),
                    Paragraph(Text(
                        "Differentiating the flow equation in its second argument at zero shows "
                            + "that the derivative of E equals E. The quotient of E by the real "
                            + "exponential then has zero derivative everywhere. Positivity fixes "
                            + "E at zero to one, so the quotient is identically one and E(1)=e."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula e = F.Id("E");
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Forall, Sp, e, Colon, Sp, reals, Sp, To, Sp, reals, Comma, RowBreak,
            Open,
                Open, Forall, Sp, t, InMacro, Sp, reals, Comma, Sp,
                    D(0), Sp, Lt, Sp, e, Open, t, Close, Close,
                Sp, Land, Sp,
                e, Sp, InMacro, Sp, F.Id("C"), Caret, Grp(D(1)),
                    Open, reals, Comma, Sp, reals, Close,
                Sp, Land, Sp,
                Open, Forall, Sp, x, Comma, Sp, y, InMacro, Sp, reals, Comma, Sp,
                    e, Open, x, Sp, Plus, Sp, y, Close, Sp, Eq, Sp,
                    e, Open, x, Close, e, Open, y, Close, Close,
                Sp, Land, Sp,
                e, Apos, Open, D(0), Close, Sp, Eq, Sp, D(1),
            Close, RowBreak,
            Sp, Rightarrow, Sp, Forall, Sp, x, InMacro, Sp, reals, Comma, Sp,
                e, Open, x, Close, Sp, Eq, Sp,
                F.Id("e"), Caret, Grp(x), Dot));
    }
}
