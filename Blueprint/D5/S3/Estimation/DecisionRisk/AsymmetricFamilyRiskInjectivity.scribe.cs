using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class AsymmetricFamilyRiskInjectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The asymmetric three-output experiment has an explicit Bayes risk, and the fixed-mass "
            + "risk queries are injective exactly below the saturation prior.",
        H("Asymmetric Family Risk and Injective Queries"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("asymmetric-three-output-experiment"),
                DeclarationHandle.Create(Prefix + "asymmetricExperiment"),
                H("The asymmetric experiment"),
                StatementSource.FromAuthor(ExperimentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two states share mass b in the first output. The residual mass D is "
                        + "placed in the second output for state zero and in the third output "
                        + "for state one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("asymmetric-zero-one-bayes-risk"),
                DeclarationHandle.Create(Prefix + "asymmetricBayesRisk"),
                H("Optimal zero-one Bayes risk"),
                StatementSource.FromAuthor(BayesRiskFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The risk is the infimum over all row-stochastic decisions from the three "
                        + "outputs to the two actions, for the prior (pi, 1 - pi) and zero-one loss."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("asymmetric-fixed-mass-fiber-risk"),
                DeclarationHandle.Create(Prefix + "asymmetricFiberRisk"),
                H("Risk along a fixed-mass fiber"),
                StatementSource.FromAuthor(FiberRiskFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fixing M and a leaves d as the fiber coordinate and sets b equal to M - a - d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("asymmetric-family-risk-injective-queries"),
                DeclarationHandle.Create(Prefix + "asymmetric_family_risk_and_injective_queries"),
                H("Piecewise risk and injectivity threshold"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive asymmetric masses with a at most d, the two likelihood "
                            + "crossings lie strictly on opposite sides of one half. Minimizing "
                            + "the error contribution separately at each output gives the four "
                            + "displayed affine pieces.")),
                    Paragraph(Text(
                        "On a fixed-mass fiber and above prior one half, the risk is a positive "
                            + "affine multiple of min(d,t). It is strictly increasing when t is "
                            + "at least the fiber endpoint L, and otherwise it is constant on a "
                            + "nontrivial terminal interval. This yields the exact injectivity "
                            + "threshold and the maximal admissible slope."))),
                DescribeRole.Theorem))));

    private static Formula ExperimentFormula()
    {
        Formula a = F.Id("a"), d = F.Id("d"), b = F.Id("b"), defect = F.Id("D");
        Formula rowZero = Tuple(b, Add(a, defect), d);
        Formula rowOne = Tuple(b, a, Add(d, defect));

        return Disp(Seq(
            Forall, Sp, TypedMany([a, d, b], Real()), Comma, RowBreak, Grp(),
            LetIn(
                [Eqn(defect, Sub(D(1), Paren(Add(b, a, d))))],
                Eqn(Call("asymmetricExperiment", a, d, b), Tuple(rowZero, rowOne))), Dot));
    }

    private static Formula BayesRiskFormula()
    {
        Formula a = F.Id("a"), d = F.Id("d"), b = F.Id("b"), pi = F.Id("pi");
        Formula state = F.Id("i"), action = F.Id("j"), decision = F.Id("delta");
        Formula prior = Call("vec", pi, Sub(D(1), pi));
        Formula loss = Seq(Open, state, Comma, Sp, action, Close, Mapsto, Sp,
            F.Text, Grp(F.Id("if"), Sp), Eqn(state, action), Sp,
            F.Text, Grp(F.Id("then"), Sp), D(0), Sp,
            F.Text, Grp(F.Id("else"), Sp), D(1));
        Formula cost = Call("finiteBayesCost", prior, loss,
            Call("asymmetricExperiment", a, d, b), decision);
        Formula decisions = Typed(decision,
            Call("FiniteMarkovKernel", Call("Fin", D(3)), Call("Fin", D(2))));

        return Disp(Seq(
            Forall, Sp, TypedMany([a, d, b, pi], Real()), Comma, RowBreak, Grp(),
            Call("asymmetricBayesRisk", a, d, b, pi), Sp, Eq, Sp,
            Call("sInf", Call("range", Seq(Open, decisions, Sp, Mapsto, Sp, cost, Close))), Dot));
    }

    private static Formula FiberRiskFormula()
    {
        Formula mass = F.Id("M"), a = F.Id("a"), pi = F.Id("pi"), d = F.Id("d");
        return Disp(Seq(
            Forall, Sp, TypedMany([mass, a, pi, d], Real()), Comma, RowBreak, Grp(),
            Call("asymmetricFiberRisk", mass, a, pi, d), Sp, Eq, Sp,
            Call("asymmetricBayesRisk", a, d, Sub(mass, a, d), pi), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula aOne = F.Id("aOne"), dOne = F.Id("dOne"), bOne = F.Id("bOne");
        Formula piOne = F.Id("piOne"), aTwo = F.Id("aTwo"), mTwo = F.Id("mTwo");
        Formula piTwo = F.Id("piTwo"), m = F.Id("M"), defect = F.Id("D");
        Formula tMinus = F.Id("tMinus"), tPlus = F.Id("tPlus");
        Formula l = F.Id("L"), u = F.Id("U"), s = F.Id("s"), c = F.Id("c");
        Formula t = F.Id("t"), fiber = F.Id("d");

        Formula riskOne = Call("asymmetricBayesRisk", aOne, dOne, bOne, piOne);
        Formula firstHypotheses = And(
            LtF(D(0), aOne), LeF(aOne, dOne), LtF(D(0), bOne),
            LtF(Add(bOne, aOne, dOne), D(1)), Member(piOne, Call("Icc", D(0), D(1))));
        Formula firstConclusion = LetIn(
            [
                Eqn(m, Add(bOne, aOne, dOne)),
                Eqn(defect, Sub(D(1), m)),
                Eqn(tMinus, Div(aOne, Add(Mul(D(2), aOne), defect))),
                Eqn(tPlus, Div(Add(dOne, defect), Add(Mul(D(2), dOne), defect)))
            ],
            And(
                And(LtF(D(0), tMinus), LtF(tMinus, Half()),
                    LtF(Half(), tPlus), LtF(tPlus, D(1))),
                ImpliesF(Member(piOne, Call("Icc", D(0), tMinus)), Eqn(riskOne, piOne)),
                ImpliesF(Member(piOne, Call("Icc", tMinus, Half())),
                    Eqn(riskOne, Add(aOne, Mul(piOne, Paren(Sub(m, Mul(D(2), aOne))))))),
                ImpliesF(Member(piOne, Call("Icc", Half(), tPlus)),
                    Eqn(riskOne, Add(Mul(m, Paren(Sub(D(1), piOne))),
                        Mul(Paren(Sub(Mul(D(2), piOne), D(1))), dOne)))),
                ImpliesF(Member(piOne, Call("Icc", tPlus, D(1))),
                    Eqn(riskOne, Sub(D(1), piOne)))));

        Formula fiberRisk = Call("asymmetricFiberRisk", mTwo, aTwo, piTwo, fiber);
        Formula fiberSet = Call("Ico", aTwo, l);
        Formula injective = Call("InjOn",
            Call("asymmetricFiberRisk", mTwo, aTwo, piTwo), fiberSet);
        Formula piStar = Div(Add(l, defect), Add(Mul(D(2), l), defect));
        Formula starInjective = Call("InjOn",
            Call("asymmetricFiberRisk", mTwo, aTwo, piStar), fiberSet);
        Formula secondHypotheses = And(
            LtF(D(0), Mul(D(2), aTwo)), LtF(Mul(D(2), aTwo), mTwo),
            LtF(mTwo, D(1)), LtF(Half(), piTwo), LeF(piTwo, D(1)));
        Formula secondConclusion = LetIn(
            [
                Eqn(defect, Sub(D(1), mTwo)),
                Eqn(l, Sub(mTwo, aTwo)),
                Eqn(u, Add(Mul(D(2), l), defect)),
                Eqn(s, Sub(Mul(D(2), piTwo), D(1))),
                Eqn(c, Mul(mTwo, Paren(Sub(D(1), piTwo)))),
                Eqn(t, Div(Mul(defect, Paren(Sub(D(1), s))), Mul(D(2), s)))
            ],
            And(
                ForallIn(fiber, fiberSet,
                    Eqn(fiberRisk, Add(c, Mul(s, MinF(fiber, t))))),
                IffF(injective, LeF(piTwo, piStar)),
                Eqn(piStar, Div(Add(D(1), Div(defect, u)), D(2))),
                ImpliesF(injective, LeF(s, Div(defect, u))),
                starInjective,
                Eqn(Sub(Mul(D(2), piStar), D(1)), Div(defect, u))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, TypedMany([aOne, dOne, bOne, piOne, aTwo, mTwo, piTwo], Real()),
            Comma, RowBreak, Grp(),
            Open, firstHypotheses, Sp, Rightarrow, Sp, firstConclusion, Close,
            Sp, Land, RowBreak, Grp(),
            Open, secondHypotheses, Sp, Rightarrow, Sp, secondConclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula TypedMany(Formula[] values, Formula type)
    {
        var items = new List<Formula>();
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(values[index]);
        }

        items.AddRange([Colon, Sp, type]);
        return Seq([.. items]);
    }

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Tuple(params Formula[] values)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(values[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula LetIn(Formula[] definitions, Formula body)
    {
        var items = new List<Formula> { F.Text, Grp(F.Id("let"), Sp), Sp };
        for (var index = 0; index < definitions.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(definitions[index]);
        }

        items.AddRange([Sp, F.Text, Grp(Sp, F.Id("in"), Sp), Sp, body]);
        return Seq([.. items]);
    }

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, RowBreak, Grp()]);
            items.Add(clauses[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Add(params Formula[] terms) => Infix(Plus, terms);

    private static Formula Sub(params Formula[] terms) => Infix(Minus, terms);

    private static Formula Mul(params Formula[] terms) => Infix(Cdot, terms);

    private static Formula Infix(Formula op, Formula[] terms)
    {
        var items = new List<Formula>();
        for (var index = 0; index < terms.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, op, Sp]);
            items.Add(terms[index]);
        }

        return Seq([.. items]);
    }

    private static Formula Div(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Half() => Div(D(1), D(2));

    private static Formula Paren(Formula value) => Seq(Open, value, Close);

    private static Formula MinF(Formula left, Formula right) =>
        Seq(Min, Sp, Open, left, Comma, Sp, right, Close);

    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);

    private static Formula LtF(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);

    private static Formula LeF(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula ImpliesF(Formula premise, Formula conclusion) =>
        Seq(Open, Open, premise, Close, Sp, Rightarrow, Sp, Open, conclusion, Close, Close);

    private static Formula IffF(Formula left, Formula right) =>
        Seq(Open, Open, left, Close, Sp, Iff, Sp, Open, right, Close, Close);

    private static Formula ForallIn(Formula value, Formula set, Formula body) =>
        Seq(Open, Forall, Sp, value, Sp, InMacro, Sp, set, Comma, Sp, body, Close);
}
