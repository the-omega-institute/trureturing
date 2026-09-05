using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class GoldenArchimedeanGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaGamma/GoldenArchimedeanGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonzero golden observer mode has one uniform positive Archimedean gap.",
        H("Golden Archimedean Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-archimedean-gap-definition"),
                DeclarationHandle.Create(Prefix + "goldenArchimedeanGap"),
                H("The fundamental golden gap"),
                StatementSource.FromAuthor(GapDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named gap is the canonical logarithmic Archimedean dispersion "
                        + "evaluated at the squared fundamental golden frequency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("archimedean-dispersion-mono"),
                DeclarationHandle.Create(Prefix + "archimedean_dispersion_mono"),
                H("The tower is monotone in squared frequency"),
                StatementSource.FromAuthor(DispersionMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Termwise logarithmic monotonicity combines with an explicit "
                        + "summable p-series majorant to compare the two infinite towers."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-archimedean-gap"),
                DeclarationHandle.Create(Prefix + "golden_archimedean_gap"),
                H("All nonzero modes share a positive gap"),
                StatementSource.FromAuthor(GapTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A nonzero integer has squared magnitude at least one, so its "
                            + "squared golden frequency dominates the fundamental one.")),
                    Paragraph(Text(
                        "Dispersion monotonicity gives the uniform lower bound, while the "
                            + "frozen nonzero-mode positivity theorem supplies strict positivity."))),
                DescribeRole.Theorem))));

    private static Formula GapDefinitionFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula index = F.Id("m");
        Formula scale = Seq(sigma, Sp, Plus, Sp, D(2), index);
        Formula scaleSquared = new Formula.Power(Grp(scale), D(2));
        Formula logPhiSquared = new Formula.Power(Grp(Call("log", Phi)), D(2));
        Formula piSquared = new Formula.Power(Grp(Pi), D(2));
        Formula denominator = Seq(logPhiSquared, Sp, Times, Sp, scaleSquared);
        Formula summand = Call("log", Seq(
            D(1), Sp, Plus, Sp, new Formula.Fraction(piSquared, denominator)));
        Formula tower = Seq(
            Sum, Underscore, Grp(index, Eq, D(0)), Caret, Grp(Infty), Sp, summand);

        return Statement(
            [Typed(sigma, Reals())],
            Seq(Call("goldenArchimedeanGap", sigma), Sp, Eq, Sp, tower));
    }

    private static Formula DispersionMonotonicityFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula lambda = F.Id("lambda");
        Formula mu = F.Id("mu");
        Formula premises = Seq(
            D(0), Sp, Lt, Sp, sigma, Comma, Sp,
            D(0), Sp, Leq, Sp, lambda, Comma, Sp,
            lambda, Sp, Leq, Sp, mu);
        Formula conclusion = Seq(
            Call("archimedeanDispersion", sigma, lambda), Sp, Leq, Sp,
            Call("archimedeanDispersion", sigma, mu));

        return Statement(
            [Typed(sigma, Reals()), Typed(lambda, Reals()), Typed(mu, Reals())],
            Seq(premises, Sp, Rightarrow, Sp, conclusion));
    }

    private static Formula GapTheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula mode = F.Id("n");
        Formula modeReal = Coerce(mode, Reals());
        Formula frequency = F.Id("goldenAngularFrequency");
        Formula modeFrequencySquared = new Formula.Power(
            Grp(Seq(modeReal, Sp, Times, Sp, frequency)), D(2));
        Formula cost = Call("archimedeanDispersion", sigma, modeFrequencySquared);
        Formula gap = Call("goldenArchimedeanGap", sigma);
        Formula modeNonzero = new Formula.Not(
            new Formula.Relation(mode, FormulaRelationOperator.Equal, D(0)));
        Formula premises = Seq(
            D(1), Sp, Lt, Sp, sigma, Comma, Sp, modeNonzero);
        Formula conclusion = Seq(
            cost, Sp, Geq, Sp, gap, Sp, Gt, Sp, D(0));

        return Statement(
            [Typed(sigma, Reals()), Typed(mode, Integers())],
            Seq(premises, Sp, Rightarrow, Sp, conclusion));
    }

    private static Formula Statement(Formula[] binders, Formula conclusion)
    {
        List<Formula> items = [Forall, Sp];
        for (int index = 0; index < binders.Length; index++)
        {
            if (index > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(binders[index]);
        }
        items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Coerce(Formula value, Formula type) =>
        Seq(Open, value, Colon, Sp, type, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
