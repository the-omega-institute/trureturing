using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class NormativeScaleChoiceReversalWithMetaDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValueScale/NormativeScaleChoiceReversalWithMeta."
            + "normative_scale_choice_reversal_with_metanormative_data";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive rescalings reverse aggregate action choice and require explicit "
            + "metanormative data when doctrine permissions have empty intersection.",
        H("Normative Scale Reversal with Metanormative Conflict Data"),
        Blocks(Describe.Lean(
            DescribeId.Create("normative-scale-choice-reversal-with-metanormative-data"),
            DeclarationHandle.Create(Declaration),
            H("Cross-doctrine choice is not fixed by probability and internal order"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public carrier is exactly two Boolean doctrines and two Boolean "
                        + "actions, with real-valued utility and probability functions. "
                        + "Both doctrine probabilities are one half, and each doctrine's "
                        + "coordinates preserve its strict internal ranking under two positive "
                        + "utility scales.")),
                Paragraph(Text(
                    "The displayed weighted sums evaluate to alpha over two and beta over "
                        + "two. The first scale therefore selects action true while the "
                        + "second selects action false, exposing the cross-theory scale "
                        + "dependence rather than hiding it in a definition.")),
                Paragraph(Text(
                    "MetaNormativeData is an independent source primitive carrying cross-"
                        + "theory scale, rights priority, worst-case and regret scores, and "
                        + "the two doctrine permission predicates. The final implication "
                        + "states directly that an empty permission intersection licenses "
                        + "no universally permitted action.")),
                Paragraph(Text(
                    "Repository and pinned-library searches found only the frozen arithmetic "
                        + "reversal theorem, which lacks the metanormative carrier and "
                        + "permission-intersection clause; no exact combined theorem was found."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(params Formula[] formulas)
    {
        Formula result = formulas[^1];
        for (var index = formulas.Length - 2; index >= 0; index--)
            result = new Formula.Logic(formulas[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula real = RealType();
        Formula alphaFirst = F.Id("alphaFirst");
        Formula betaFirst = F.Id("betaFirst");
        Formula alphaSecond = F.Id("alphaSecond");
        Formula betaSecond = F.Id("betaSecond");
        Formula probability = F.Id("probability");
        Formula utilityFirst = F.Id("utilityFirst");
        Formula utilitySecond = F.Id("utilitySecond");
        Formula metaData = F.Id("metaData");
        Formula doctrine = F.Id("doctrine");
        Formula leftAction = F.Id("leftAction");
        Formula rightAction = F.Id("rightAction");
        Formula trueValue = F.Id("true");
        Formula falseValue = F.Id("false");
        Formula permission = F.Id("permission");
        Formula firstPermission = Apply(permission, metaData, trueValue);
        Formula secondPermission = Apply(permission, metaData, falseValue);
        Formula firstSet = Call("permissionSet", metaData, trueValue);
        Formula secondSet = Call("permissionSet", metaData, falseValue);
        Formula commonPermissionEmpty = EqualTo(
            Call("intersection", firstSet, secondSet), Emptyset);

        Formula probabilityHalf = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("doctrine"),
            boolean,
            EqualTo(Apply(probability, doctrine), Seq(Frac, Grp(D(1)), Grp(D(2)))));

        Formula firstCoordinates = And(
            EqualTo(Apply(utilityFirst, trueValue, trueValue), alphaFirst),
            EqualTo(Apply(utilityFirst, trueValue, falseValue), D(0)),
            EqualTo(Apply(utilityFirst, falseValue, trueValue), D(0)),
            EqualTo(Apply(utilityFirst, falseValue, falseValue), betaFirst));
        Formula secondCoordinates = And(
            EqualTo(Apply(utilitySecond, trueValue, trueValue), alphaSecond),
            EqualTo(Apply(utilitySecond, trueValue, falseValue), D(0)),
            EqualTo(Apply(utilitySecond, falseValue, trueValue), D(0)),
            EqualTo(Apply(utilitySecond, falseValue, falseValue), betaSecond));
        Formula firstRanking = And(
            Greater(Apply(utilityFirst, trueValue, trueValue),
                Apply(utilityFirst, trueValue, falseValue)),
            Greater(Apply(utilityFirst, falseValue, falseValue),
                Apply(utilityFirst, falseValue, trueValue)));
        Formula secondRanking = And(
            Greater(Apply(utilitySecond, trueValue, trueValue),
                Apply(utilitySecond, trueValue, falseValue)),
            Greater(Apply(utilitySecond, falseValue, falseValue),
                Apply(utilitySecond, falseValue, trueValue)));
        Formula rankingInvariance = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("doctrine", boolean), Bound("leftAction", boolean),
                Bound("rightAction", boolean)],
            new Formula.Logic(
                Greater(Apply(utilityFirst, doctrine, leftAction),
                    Apply(utilityFirst, doctrine, rightAction)),
                FormulaLogicOperator.Iff,
                Greater(Apply(utilitySecond, doctrine, leftAction),
                    Apply(utilitySecond, doctrine, rightAction))));

        Formula firstActionAValue = Seq(
            Apply(probability, trueValue), Sp, Cdot, Sp,
            Apply(utilityFirst, trueValue, trueValue), Sp, Plus, Sp,
            Apply(probability, falseValue), Sp, Cdot, Sp,
            Apply(utilityFirst, falseValue, trueValue));
        Formula firstActionBValue = Seq(
            Apply(probability, trueValue), Sp, Cdot, Sp,
            Apply(utilityFirst, trueValue, falseValue), Sp, Plus, Sp,
            Apply(probability, falseValue), Sp, Cdot, Sp,
            Apply(utilityFirst, falseValue, falseValue));
        Formula secondActionAValue = Seq(
            Apply(probability, trueValue), Sp, Cdot, Sp,
            Apply(utilitySecond, trueValue, trueValue), Sp, Plus, Sp,
            Apply(probability, falseValue), Sp, Cdot, Sp,
            Apply(utilitySecond, falseValue, trueValue));
        Formula secondActionBValue = Seq(
            Apply(probability, trueValue), Sp, Cdot, Sp,
            Apply(utilitySecond, trueValue, falseValue), Sp, Plus, Sp,
            Apply(probability, falseValue), Sp, Cdot, Sp,
            Apply(utilitySecond, falseValue, falseValue));

        Formula firstAggregate = And(
            EqualTo(firstActionAValue, Seq(Frac, Grp(alphaFirst), Grp(D(2)))),
            EqualTo(firstActionBValue, Seq(Frac, Grp(betaFirst), Grp(D(2)))));
        Formula secondAggregate = And(
            EqualTo(secondActionAValue, Seq(Frac, Grp(alphaSecond), Grp(D(2)))),
            EqualTo(secondActionBValue, Seq(Frac, Grp(betaSecond), Grp(D(2)))));
        Formula reversal = And(
            Greater(firstActionAValue, firstActionBValue),
            Greater(secondActionBValue, secondActionAValue));
        Formula noCommonAction = Implies(
            commonPermissionEmpty,
            new Formula.Not(new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("action"),
                boolean,
                And(Apply(permission, metaData, trueValue, F.Id("action")),
                    Apply(permission, metaData, falseValue, F.Id("action"))))));

        Formula hypotheses = And(
            Greater(alphaFirst, D(0)), Greater(betaFirst, D(0)),
            Greater(alphaSecond, D(0)), Greater(betaSecond, D(0)),
            Greater(alphaFirst, betaFirst), Greater(betaSecond, alphaSecond),
            probabilityHalf, firstCoordinates, secondCoordinates,
            commonPermissionEmpty);
        Formula conclusion = And(
            probabilityHalf, firstCoordinates, secondCoordinates,
            firstRanking, secondRanking, rankingInvariance,
            firstAggregate, secondAggregate, reversal, noCommonAction);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("alphaFirst", real), Bound("betaFirst", real),
                Bound("alphaSecond", real), Bound("betaSecond", real),
                Bound("probability", Arrow(boolean, real)),
                Bound("utilityFirst", Arrow(boolean, Arrow(boolean, real))),
                Bound("utilitySecond", Arrow(boolean, Arrow(boolean, real))),
                Bound("metaData", F.Id("MetaNormativeData")),
            ],
            Implies(hypotheses, conclusion)));
    }
}
