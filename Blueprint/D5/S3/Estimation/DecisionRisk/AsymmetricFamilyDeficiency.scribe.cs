using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class AsymmetricFamilyDeficiencyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency."
            + "asymmetric_family_deficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deficiency is directed along each fixed-mass fibre of the asymmetric experiment.",
        H("Asymmetric Family Deficiency"),
        Blocks(Describe.Lean(
            DescribeId.Create("asymmetric-family-deficiency"),
            DeclarationHandle.Create(Declaration),
            H("Exact directed deficiencies on a fixed-mass fibre"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Increasing the second label mass is an exact garbling: the common output "
                        + "is split between itself and the second label while both labels remain fixed.")),
                Paragraph(Text(
                    "In the reverse direction, the optimal error is the positive quantity gamma. "
                        + "A zero-one Bayes risk comparison gives the lower bound, and a kernel that "
                        + "moves mass from the third output to the common output attains it in both states."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a"), mass = F.Id("M"), dOne = F.Id("dOne");
        Formula dTwo = F.Id("dTwo"), defect = F.Id("D"), length = F.Id("L");
        Formula qOne = F.Id("QOne"), qTwo = F.Id("QTwo"), gamma = F.Id("gamma");
        Formula twoA = Mul(D(2), a);
        Formula qOneValue = Call("asymmetricExperiment", a, dOne, Paren(Sub(length, dOne)));
        Formula qTwoValue = Call("asymmetricExperiment", a, dTwo, Paren(Sub(length, dTwo)));
        Formula gammaValue = Div(
            Mul(defect, Paren(Sub(dTwo, dOne))),
            Paren(Add(Mul(D(2), dTwo), defect)));
        Formula conclusion = And(
            Eqn(Call("finiteDeficiency", qTwo, qOne), D(0)),
            Eqn(Call("finiteDeficiency", qOne, qTwo), Call("ofReal", gamma)),
            LtF(D(0), gamma));
        Formula hypotheses = Implies(
            LtF(D(0), twoA),
            LtF(twoA, mass),
            LtF(mass, D(1)),
            LeF(a, dOne),
            LtF(dOne, dTwo),
            LtF(dTwo, Paren(Sub(mass, a))),
            LetIn(
                [
                    Eqn(defect, Sub(D(1), mass)),
                    Eqn(length, Sub(mass, a)),
                    Eqn(qOne, qOneValue),
                    Eqn(qTwo, qTwoValue),
                    Eqn(gamma, gammaValue)
                ],
                conclusion));

        return Disp(Seq(
            Forall, Sp, TypedMany([a, mass, dOne, dTwo], Real()), Comma,
            RowBreak, Grp(), hypotheses, Dot));
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

    private static Formula Implies(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Rightarrow, Sp]);
            items.AddRange([Open, clauses[index], Close]);
            if (index + 1 < clauses.Length) items.AddRange([RowBreak, Grp()]);
        }

        return Seq([.. items]);
    }

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, RowBreak, Grp()]);
            items.AddRange([Open, clauses[index], Close]);
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

    private static Formula Paren(Formula value) => Seq(Open, value, Close);

    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);

    private static Formula LtF(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);

    private static Formula LeF(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
}
