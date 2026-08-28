using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class BenefitProbabilityBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two Boolean potential-outcome marginals give algebraic bounds on the "
            + "benefit mass of every normalized nonnegative joint law.",
        H("Benefit Probability Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("benefit-probability-bounds"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Causal/BenefitProbabilityBounds."
                        + "benefit_probability_bounds"),
                H("Potential-outcome marginals bound the benefit probability"),
                StatementSource.FromAuthor(BoundsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let mass be a normalized nonnegative joint law of the Boolean pair "
                            + "of potential outcomes. The benefit probability is the mass of "
                            + "the false-true response type.")),
                    Paragraph(Text(
                        "The treatment-one marginal is the sum of the false-true and true-true "
                            + "masses. The treatment-zero marginal is the sum of the true-false "
                            + "and true-true masses.")),
                    Paragraph(Text(
                        "Nonnegativity of the true-false cell gives the lower marginal-difference "
                            + "bound. Nonnegativity of the true-true and false-false cells gives "
                            + "the two upper bounds."))),
                DescribeRole.Theorem))));

    private static Formula BoundsFormula()
    {
        Formula boolType = F.Id("Bool");
        Formula realType = F.Id("Real");
        Formula pairType = Call("Prod", boolType, boolType);
        Formula mass = F.Id("mass");
        Formula pair = F.Id("pair");
        Formula zero = new Formula.Number(0);
        Formula one = new Formula.Number(1);
        Formula falseValue = F.Id("false");
        Formula trueValue = F.Id("true");

        Formula ff = Apply(mass, Pair(falseValue, falseValue));
        Formula benefit = Apply(mass, Pair(falseValue, trueValue));
        Formula harmful = Apply(mass, Pair(trueValue, falseValue));
        Formula tt = Apply(mass, Pair(trueValue, trueValue));
        Formula treatmentOneMarginal = Add(benefit, tt);
        Formula treatmentZeroMarginal = Add(harmful, tt);

        Formula nonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("pair", pairType)],
            Relation(zero, FormulaRelationOperator.LessThanOrEqual, Apply(mass, pair)));
        Formula normalized = Equal(Add(Add(Add(ff, benefit), harmful), tt), one);
        Formula lowerBound = Call(
            "max",
            zero,
            Subtract(treatmentOneMarginal, treatmentZeroMarginal));
        Formula upperBound = Call(
            "min",
            treatmentOneMarginal,
            Subtract(one, treatmentZeroMarginal));
        Formula conclusion = And(
            Relation(lowerBound, FormulaRelationOperator.LessThanOrEqual, benefit),
            Relation(benefit, FormulaRelationOperator.LessThanOrEqual, upperBound));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("mass", new Formula.TypeArrow(pairType, realType))],
            Implies(And(Grp(nonnegative), normalized), conclusion)));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Pair(Formula first, Formula second) =>
        Call("pair", first, second);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator relation,
        Formula right) => new Formula.Relation(left, relation, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
