using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaCore;

internal sealed class LocalSpectralFloorDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaCore/LocalSpectralFloor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity sectors and the local positive cone determine the full spectral floor.",
        H("Local Spectral Floors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parity-spectral-infimum"),
                DeclarationHandle.Create(Prefix + "parity_spectral_infimum"),
                H("Parity decomposition of the spectral infimum"),
                StatementSource.FromAuthor(ParityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The full carrier is the even-odd product. Additivity of energy and squared "
                        + "norm makes every mixed Rayleigh quotient a positive weighted average "
                        + "of the two sector quotients, while pure-sector vectors attain both "
                        + "comparison infima."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("white-noise-cone-margin"),
                DeclarationHandle.Create(Prefix + "white_noise_cone_margin"),
                H("White-noise cone margin"),
                StatementSource.FromAuthor(ConeMarginFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An admissible white-noise floor is exactly a lower bound of the nonzero "
                        + "Rayleigh-value set. The supremum of all such lower bounds is therefore "
                        + "the spectral infimum."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Not(Equal(left, right));

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula ParityFormula()
    {
        Formula type = F.Id("Type"), real = Call("Real");
        Formula even = F.Id("Even"), odd = F.Id("Odd");
        Formula evenEnergy = F.Id("evenEnergy"), evenNormSq = F.Id("evenNormSq");
        Formula oddEnergy = F.Id("oddEnergy"), oddNormSq = F.Id("oddNormSq");
        Formula e = F.Id("e"), o = F.Id("o"), r = F.Id("r");
        Formula fullValues = F.Id("fullValues"), evenValues = F.Id("evenValues");
        Formula oddValues = F.Id("oddValues");
        Formula Apply(Formula function, Formula value) => Call("apply", function, value);
        Formula EvenRatio(Formula value) =>
            Call("div", Apply(evenEnergy, value), Apply(evenNormSq, value));
        Formula OddRatio(Formula value) =>
            Call("div", Apply(oddEnergy, value), Apply(oddNormSq, value));
        Formula fullPredicate = Exists(
            [Bound("e", even), Bound("o", odd)],
            And(
                NotEqual(Call("pair", e, o), Call("pair", D(0), D(0))),
                Equal(r, Call("div",
                    Call("add", Apply(evenEnergy, e), Apply(oddEnergy, o)),
                    Call("add", Apply(evenNormSq, e), Apply(oddNormSq, o))))));
        Formula evenPredicate = Exists(
            [Bound("e", even)],
            And(NotEqual(e, D(0)), Equal(r, EvenRatio(e))));
        Formula oddPredicate = Exists(
            [Bound("o", odd)],
            And(NotEqual(o, D(0)), Equal(r, OddRatio(o))));
        Formula fullSet = new Formula.SetBuilder(fullPredicate, r, real);
        Formula evenSet = new Formula.SetBuilder(evenPredicate, r, real);
        Formula oddSet = new Formula.SetBuilder(oddPredicate, r, real);
        Formula definitions = Seq(
            Operatorname, Grp(F.Id("let")), Sp, fullValues, Sp, Eq, Sp, fullSet, Comma, Sp,
            Operatorname, Grp(F.Id("let")), Sp, evenValues, Sp, Eq, Sp, evenSet, Comma, Sp,
            Operatorname, Grp(F.Id("let")), Sp, oddValues, Sp, Eq, Sp, oddSet, Comma, Sp,
            Equal(Call("sInf", fullValues),
                Call("min", Call("sInf", evenValues), Call("sInf", oddValues))));
        Formula assumptions = All(
            Call("Zero", even),
            Call("Zero", odd),
            Call("Nontrivial", even),
            Call("Nontrivial", odd),
            Equal(Apply(evenEnergy, D(0)), D(0)),
            Equal(Apply(oddEnergy, D(0)), D(0)),
            Equal(Apply(evenNormSq, D(0)), D(0)),
            Equal(Apply(oddNormSq, D(0)), D(0)),
            ForAll([Bound("e", even)],
                Implies(NotEqual(e, D(0)), Less(D(0), Apply(evenNormSq, e)))),
            ForAll([Bound("o", odd)],
                Implies(NotEqual(o, D(0)), Less(D(0), Apply(oddNormSq, o)))),
            Call("BddBelow", evenSet),
            Call("BddBelow", oddSet));

        return F.Disp(ForAll(
            [
                Bound("Even", type),
                Bound("Odd", type),
                Bound("evenEnergy", new Formula.TypeArrow(even, real)),
                Bound("evenNormSq", new Formula.TypeArrow(even, real)),
                Bound("oddEnergy", new Formula.TypeArrow(odd, real)),
                Bound("oddNormSq", new Formula.TypeArrow(odd, real)),
            ],
            Implies(assumptions, definitions)));
    }

    private static Formula ConeMarginFormula()
    {
        Formula type = F.Id("Type"), real = Call("Real");
        Formula space = F.Id("H"), quadratic = F.Id("quadratic"), normSq = F.Id("normSq");
        Formula f = F.Id("f"), r = F.Id("r"), lambda = F.Id("lambda");
        Formula rayleighValues = F.Id("rayleighValues");
        Formula admissibleFloors = F.Id("admissibleFloors");
        Formula Apply(Formula function, Formula value) => Call("apply", function, value);
        Formula rayleighPredicate = Exists(
            [Bound("f", space)],
            And(NotEqual(f, D(0)), Equal(r,
                Call("div", Apply(quadratic, f), Apply(normSq, f)))));
        Formula rayleighSet = new Formula.SetBuilder(rayleighPredicate, r, real);
        Formula floorPredicate = ForAll(
            [Bound("f", space)],
            AtMost(D(0), Call("sub", Apply(quadratic, f),
                Call("mul", lambda, Apply(normSq, f)))));
        Formula floorSet = new Formula.SetBuilder(floorPredicate, lambda, real);
        Formula definitions = Seq(
            Operatorname, Grp(F.Id("let")), Sp, rayleighValues, Sp, Eq, Sp,
            rayleighSet, Comma, Sp,
            Operatorname, Grp(F.Id("let")), Sp, admissibleFloors, Sp, Eq, Sp,
            floorSet, Comma, Sp,
            Equal(Call("sInf", rayleighValues), Call("sSup", admissibleFloors)));
        Formula assumptions = All(
            Call("Zero", space),
            Call("Nontrivial", space),
            Equal(Apply(quadratic, D(0)), D(0)),
            Equal(Apply(normSq, D(0)), D(0)),
            ForAll([Bound("f", space)],
                Implies(NotEqual(f, D(0)), Less(D(0), Apply(normSq, f)))),
            Call("BddBelow", rayleighSet));

        return F.Disp(ForAll(
            [
                Bound("H", type),
                Bound("quadratic", new Formula.TypeArrow(space, real)),
                Bound("normSq", new Formula.TypeArrow(space, real)),
            ],
            Implies(assumptions, definitions)));
    }
}
