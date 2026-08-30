using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.NamingRate;

internal sealed class LogarithmicMarginDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var type = F.Id("Type");
        var proposition = F.Id("Prop");
        var natural = F.Id("N");
        var real = F.Id("R");
        var witnessType = F.Id("Witness");
        var witness = F.Id("u");
        var implements = F.Id("implements");
        var runningTime = F.Id("runningTime");
        var timeBound = F.Id("timeBound");
        var boundedNameCost = F.Id("boundedNameCost");
        var error = F.Id("error");
        var n0 = new Formula.Subscript(F.Id("n"), D(0));
        var n = F.Id("n");
        var realN = Call("castReal", n);
        var logarithmic = Call(
            "lambda",
            Call("typed", n, natural),
            Call("log", realN));
        var bigO = Call("IsBigO", error, F.Id("atTop"), logarithmic);
        var fast = Call(
            "IsFastWitness", implements, runningTime, timeBound, n, witness);
        var longName = Call(
            "HasLongName", boundedNameCost, error, n, witness);
        var shortName = Call(
            "HasShortName", implements, boundedNameCost, n, witness);
        var slow = Call("IsSlowWitness", runningTime, timeBound, n, witness);
        var margin = Seq(
            Frac, Grp(realN), Grp(D(2)), Sp, Minus, Sp, Apply(error, n),
            Sp, Gt, Sp, Frac, Grp(realN), Grp(D(4)));
        var fastImpliesLong = Seq(
            Forall, Sp, Typed(n, natural), Comma, Sp,
            Typed(witness, witnessType), Comma, Sp,
            fast, Sp, Rightarrow, Sp, longName);
        var shortImpliesSlow = Seq(
            Forall, Sp, Typed(witness, witnessType), Comma, Sp,
            shortName, Sp, Rightarrow, Sp, slow);
        var eventualContrapositive = Seq(
            Exists, Sp, Typed(n0, natural), Comma, Sp,
            Forall, Sp, Typed(n, natural), Comma, Sp,
            n, Sp, Ge, Sp, n0, Sp, Rightarrow, Sp,
            Open, margin, Sp, Land, Sp, shortImpliesSlow, Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "A logarithmic margin turns fast-implies-long into short-implies-slow.",
            H("The Logarithmic Contrapositive Margin"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("a-logarithmic-error-eventually-leaves-a-quarter-scale-margin"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/NamingRate/LogarithmicMargin." +
                        "logarithmic_error_eventually_leaves_quarter_margin"),
                    H("The quarter-short witnesses are eventually slow"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, Typed(witnessType, type), Comma, Sp,
                        Typed(implements, Seq(
                            natural, Sp, To, Sp, witnessType, Sp, To, Sp, proposition)),
                        Comma, Sp,
                        Typed(runningTime, Seq(
                            natural, Sp, To, Sp, witnessType, Sp, To, Sp, natural)),
                        Comma, Sp,
                        Typed(timeBound, Seq(natural, Sp, To, Sp, natural)),
                        Comma, Sp,
                        Typed(boundedNameCost, Seq(
                            natural, Sp, To, Sp, witnessType, Sp, To, Sp, natural)),
                        Comma, Sp,
                        Forall, Sp, Typed(error, Seq(natural, Sp, To, Sp, real)), Comma, Sp,
                        Open, bigO, Sp, Land, Sp, fastImpliesLong, Close,
                        Sp, Rightarrow, Sp, eventualContrapositive, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The public predicates retain the source's witness semantics. A fast " +
                            "witness is valid and runs within timeBound(n); a long name reaches " +
                            "n / 2 - error(n); a short witness is valid and has boundedNameCost " +
                            "at most n / 4; and a slow witness exceeds timeBound(n).")),
                        Paragraph(Text(
                            "Clause (i), fast implies long, is the public premise. Clause (ii) is " +
                            "the eventual conclusion: the strict n / 2 - error(n) > n / 4 margin " +
                            "holds and every quarter-short valid witness is slow. Assuming a short " +
                            "witness were not slow would make it fast, contradicting clause (i) " +
                            "across the displayed margin.")),
                        Paragraph(Text(
                            "Pinned Mathlib supplies Real.isLittleO_log_id_atTop. The source uses " +
                            "base-two logarithms, while Lean's Real.log is natural logarithm; their " +
                            "positive constant-factor conversion gives the same big-O class. The " +
                            "helper restricts the real asymptotic to natural inputs and obtains the " +
                            "explicit quarter-margin."))),
                    DescribeRole.Theorem)),
            []));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
}
