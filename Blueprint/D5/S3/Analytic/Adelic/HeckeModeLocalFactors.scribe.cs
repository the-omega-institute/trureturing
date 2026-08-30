using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class HeckeModeLocalFactorsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Adelic/HeckeModeLocalFactors.hecke_mode_local_factors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Split primes alone carry the regulator-mode dependence of the golden local factors.",
        H("Hecke Mode Local Factors"),
        Blocks(Describe.Lean(
            DescribeId.Create("hecke-mode-local-factors"),
            DeclarationHandle.Create(Declaration),
            H("Split, inert, and ramified local factors"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A local factor is constructed from its prime-ideal place data. Each "
                        + "place contributes its norm and regulator phase to one Euler "
                        + "factor, and the contributions are multiplied.")),
                Paragraph(Text(
                    "The canonical quadratic character selects two conjugate norm-p places "
                        + "on the split branch, one zero-phase norm-p-squared place on the "
                        + "inert branch, and one zero-phase norm-p place on the ramified "
                        + "branch.")),
                Paragraph(Text(
                    "Multiplying the conjugate split factors gives the cosine denominator. "
                        + "The zero phases make the inert and ramified factors independent "
                        + "of the mode. The canonical local branch operator then confines "
                        + "all possible mode dependence to its determinant-one branch."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula integer = Call("Int");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula natural = Call("Nat");
        Formula real = Call("Real");
        Formula modeOne = F.Id("mode1");
        Formula modeTwo = F.Id("mode2");
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula theta = F.Id("theta");
        Formula character = Call("legendreSym", D(5), p);
        Formula splitCondition = EqualTo(character, D(1));
        Formula inertCondition = EqualTo(character, Seq(Minus, D(1)));
        Formula pToMinusS = new Formula.Power(p, Grp(Seq(Minus, s)));
        Formula pToMinusTwoS = new Formula.Power(
            p,
            Grp(Seq(Minus, Open, D(2), Sp, Times, Sp, s, Close)));
        Formula cosine = Call(
            "cos",
            Seq(modeOne, Sp, Times, Sp, theta));
        Formula splitDenominator = Seq(
            D(1), Sp, Minus, Sp,
            D(2), Sp, Times, Sp, cosine, Sp, Times, Sp, pToMinusS,
            Sp, Plus, Sp, pToMinusTwoS);
        Formula splitFactor = Inverse(splitDenominator);
        Formula inertFactor = Inverse(Seq(D(1), Sp, Minus, Sp, pToMinusTwoS));
        Formula ramifiedFactor = Inverse(Seq(
            D(1), Sp, Minus, Sp,
            new Formula.Power(D(5), Grp(Seq(Minus, s)))));
        Formula localOne = LocalFactor(p, theta, modeOne, s);
        Formula localTwo = LocalFactor(p, theta, modeTwo, s);
        Formula ramifiedLocal = LocalFactor(D(5), theta, modeOne, s);
        Formula splitClause = Implies(splitCondition, EqualTo(localOne, splitFactor));
        Formula inertClause = Implies(inertCondition, EqualTo(localOne, inertFactor));
        Formula inertIndependence = Implies(inertCondition, EqualTo(localOne, localTwo));
        Formula ramifiedClause = EqualTo(ramifiedLocal, ramifiedFactor);
        Formula nonsplitCondition = NotEqualTo(
            Call("det", Call("goldenLocalBranchOperator", p)),
            D(1));
        Formula supportClause = Implies(nonsplitCondition, EqualTo(localOne, localTwo));
        Formula conclusions = And(
            splitClause,
            And(
                inertClause,
                And(inertIndependence, And(ramifiedClause, supportClause))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mode1", integer),
                Bound("mode2", integer),
                Bound("s", complex),
                Bound("p", natural),
                Bound("theta", real),
            ],
            Implies(Call("Prime", p), conclusions)));
    }

    private static Formula Inverse(Formula value) =>
        new Formula.Power(Seq(Open, value, Close), Seq(Minus, D(1)));

    private static Formula LocalFactor(
        Formula prime,
        Formula theta,
        Formula mode,
        Formula s) =>
        Call(
            "localHeckeEulerFactor",
            Call("goldenLocalPrimePlaces", prime, theta),
            mode,
            s);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
