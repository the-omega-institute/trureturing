using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Fredholm;

internal sealed class NewmanDeterminantThresholdDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Fredholm/NewmanDeterminantThreshold."
            + "newman_determinant_threshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized Fredholm, total-positivity, and Stieltjes criteria define the same "
            + "nondegenerate Newman completion threshold.",
        H("Newman Determinant Threshold"),
        Blocks(Describe.Lean(
            DescribeId.Create("normalized-newman-determinant-threshold"),
            DeclarationHandle.Create(Declaration),
            H("The three normalized completion criteria have one threshold"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each real time, F, P_infinity, and S denote respectively the "
                        + "positive trace-class Fredholm representation criterion, the "
                        + "PF-infinity coefficient criterion, and the reciprocal-zero "
                        + "Stieltjes moment criterion. The pinned library has no countable "
                        + "trace-class determinant API, so these analytic criteria enter as "
                        + "typed predicates rather than as invented operator definitions.")),
                Paragraph(Text(
                    "The original unconditional equivalence is false: a PF-infinity "
                        + "generating function may contain an exponential factor, with exp(x) "
                        + "as the basic example, and therefore need not be a pure determinant "
                        + "det(I + x U). The displayed pointwise bridge is the necessary "
                        + "no-exponential-factor normalization hypothesis.")),
                Paragraph(Text(
                    "The Fredholm feasible-time set is required to be nonempty and bounded "
                        + "below. These premises prevent Lean's real convention sInf(empty) = 0 "
                        + "from turning the threshold into a silent degenerate value.")),
                Paragraph(Text(
                    "Pointwise equivalence gives equality of all three feasible-time sets. "
                        + "Congruence of sInf gives the threshold identities, while Mathlib's "
                        + "isGLB_csInf proves that every displayed threshold is the genuine "
                        + "greatest lower bound. A companion theorem transports feasible-time "
                        + "witnesses in every direction."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(Grp(left), Sp, Iff, Sp, Grp(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = Seq(Grp(result), Sp, Land, Sp, Grp(clauses[index]));
        }

        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula fredholm = F.Id("F");
        Formula pfInfinity = new Formula.Subscript(F.Id("P"), Infty);
        Formula stieltjes = F.Id("S");
        Formula time = F.Id("t");
        Formula fredholmTimes = new Formula.Subscript(F.Id("T"), fredholm);
        Formula pfTimes = new Formula.Subscript(F.Id("T"), pfInfinity);
        Formula stieltjesTimes = new Formula.Subscript(F.Id("T"), stieltjes);
        Formula fredholmThreshold = new Formula.Subscript(Lambda, fredholm);
        Formula pfThreshold = new Formula.Subscript(Lambda, pfInfinity);
        Formula stieltjesThreshold = new Formula.Subscript(Lambda, stieltjes);
        Formula functionType = Seq(real, Sp, To, Sp, prop);

        Formula pointwiseBridge = Seq(
            Forall, Sp, time, Sp, InMacro, Sp, real, Comma, Sp,
            And(
                IffFormula(Apply(fredholm, time), Apply(pfInfinity, time)),
                IffFormula(Apply(fredholm, time), Apply(stieltjes, time))));
        Formula hypotheses = And(
            pointwiseBridge,
            Call("Nonempty", fredholmTimes),
            Call("BddBelow", fredholmTimes));
        Formula conclusion = And(
            EqualTo(fredholmTimes, pfTimes),
            EqualTo(fredholmTimes, stieltjesTimes),
            EqualTo(fredholmThreshold, pfThreshold),
            EqualTo(fredholmThreshold, stieltjesThreshold),
            Call("IsGLB", fredholmTimes, fredholmThreshold),
            Call("IsGLB", pfTimes, pfThreshold),
            Call("IsGLB", stieltjesTimes, stieltjesThreshold));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, fredholm, Comma, Sp, pfInfinity, Comma, Sp, stieltjes,
                Colon, Sp, functionType, Comma, RowBreak, Grp(),
            fredholmTimes, Sp, Colon, Eq, Sp,
                new Formula.SetBuilder(Apply(fredholm, time), time, real), Comma,
                RowBreak, Grp(),
            pfTimes, Sp, Colon, Eq, Sp,
                new Formula.SetBuilder(Apply(pfInfinity, time), time, real), Comma,
                RowBreak, Grp(),
            stieltjesTimes, Sp, Colon, Eq, Sp,
                new Formula.SetBuilder(Apply(stieltjes, time), time, real), Comma,
                RowBreak, Grp(),
            fredholmThreshold, Sp, Colon, Eq, Sp, Call("sInf", fredholmTimes), Comma,
                Sp, pfThreshold, Sp, Colon, Eq, Sp, Call("sInf", pfTimes), Comma,
                Sp, stieltjesThreshold, Sp, Colon, Eq, Sp, Call("sInf", stieltjesTimes),
                Comma, RowBreak, Grp(),
            Grp(hypotheses), Sp, Rightarrow, Sp, Grp(conclusion), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
