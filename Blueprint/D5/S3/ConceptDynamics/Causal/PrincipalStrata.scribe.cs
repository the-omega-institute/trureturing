using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class PrincipalStrataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An almost-sure monotone Boolean response law has three possible principal strata, "
            + "with masses fixed by the two potential-outcome marginals.",
        H("Principal Strata Under Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monotone-boolean-response-has-three-principal-strata"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Causal/PrincipalStrata.principal_strata"),
                H("A monotone Boolean response has three principal strata"),
                StatementSource.FromAuthor(PrincipalStrataFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let mass be a normalized nonnegative joint law on the Boolean pair "
                            + "of potential outcomes. Almost-sure monotonicity requires every "
                            + "positive-mass pair with first coordinate true to have second "
                            + "coordinate true.")),
                    Paragraph(Text(
                        "The harmful pair therefore has zero mass. Expanding normalization "
                            + "then identifies the never, benefit, and always masses as one "
                            + "minus the treatment-one marginal, the difference of the two "
                            + "marginals, and the treatment-zero marginal, respectively."))),
                DescribeRole.Theorem))));

    private static Formula PrincipalStrataFormula()
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
        Formula ft = Apply(mass, Pair(falseValue, trueValue));
        Formula tf = Apply(mass, Pair(trueValue, falseValue));
        Formula tt = Apply(mass, Pair(trueValue, trueValue));
        Formula treatmentOneMarginal = Add(ft, tt);
        Formula treatmentZeroMarginal = Add(tf, tt);

        Formula nonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("pair", pairType)],
            Relation(zero, FormulaRelationOperator.LessThanOrEqual, Apply(mass, pair)));
        Formula normalized = Equal(Add(Add(Add(ff, ft), tf), tt), one);
        Formula monotone = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("pair", pairType)],
            Implies(
                And(
                    Relation(zero, FormulaRelationOperator.LessThan, Apply(mass, pair)),
                    Equal(Call("fst", pair), trueValue)),
                Equal(Call("snd", pair), trueValue)));

        Formula conclusion = And(
            Equal(tf, zero),
            And(
                Equal(ff, Subtract(one, treatmentOneMarginal)),
                And(
                    Equal(ft, Subtract(treatmentOneMarginal, treatmentZeroMarginal)),
                    Equal(tt, treatmentZeroMarginal))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("mass", new Formula.TypeArrow(pairType, realType))],
            Implies(And(nonnegative, And(normalized, monotone)), conclusion)));
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
