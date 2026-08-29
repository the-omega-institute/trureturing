using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Evidence;

internal sealed class PositiveSupportNonexplosionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Evidence/PositiveSupportNonexplosion."
            + "positive_support_nonexplosion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both-supported evidence supplies a countermodel to positive-support explosion.",
        H("Positive-Support Non-Explosion"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-support-nonexplosion"),
            DeclarationHandle.Create(Declaration),
            H("Both-supported premises do not entail an unsupported conclusion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Over an arbitrary formula carrier, choose any distinct proposition, its "
                        + "negation, and conclusion. The proposition receives the canonical "
                        + "both-supported value, while the value of its negation is obtained "
                        + "by swapping the two support coordinates.")),
                Paragraph(Text(
                    "Both premises therefore have positive support. The arbitrary conclusion "
                        + "receives neither positive nor negative support, while every other "
                        + "formula may receive the same unsupported value. This valuation "
                        + "refutes positive-support entailment of that conclusion.")),
                Paragraph(Text(
                    "The same witness has inconsistent premise evidence while the consequence "
                        + "relation remains non-explosive: an unsupported conclusion is not "
                        + "made supported merely by the conflict."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula proposition = F.Id("proposition");
        Formula negatedProposition = F.Id("negatedProposition");
        Formula conclusion = F.Id("conclusion");
        Formula entails = F.Id("positivelyEntails");
        Formula valuation = F.Id("valuation");
        Formula candidate = F.Id("candidateValuation");
        Formula formulaCarrier = F.Id("Formula");
        Formula type = Call("Type");
        Formula evidenceValue = Call("EvidenceValue");
        Formula propositionType = F.Id("Prop");
        Formula valuationType = new Formula.TypeArrow(formulaCarrier, evidenceValue);
        Formula bothSupported = Call("bothSupported");
        Formula neitherSupported = Pair(F.Id("false"), F.Id("false"));

        Formula At(Formula function, Formula argument) =>
            new Formula.Apply(function, [argument]);
        Formula Positive(Formula value) =>
            Equal(Call("fst", value), F.Id("true"));
        Formula NegationLaw(Formula function) => Equal(
            At(function, negatedProposition),
            Call("swap", At(function, proposition)));
        Formula PremisesSupported(Formula function) => All(
            Positive(At(function, proposition)),
            Positive(At(function, negatedProposition)));
        Formula EntailmentBody(Formula function) => Implies(
            NegationLaw(function),
            Implies(
                PremisesSupported(function),
                Positive(At(function, conclusion))));

        Formula entailmentDefinition = ForAll(
            [Bound("candidateValuation", valuationType)],
            EntailmentBody(candidate));
        Formula witness = Exists(
            [Bound("valuation", valuationType)],
            All(
                Equal(At(valuation, proposition), bothSupported),
                NegationLaw(valuation),
                Positive(At(valuation, proposition)),
                Positive(At(valuation, negatedProposition)),
                Equal(At(valuation, conclusion), neitherSupported),
                Equal(Call("fst", At(valuation, conclusion)), F.Id("false")),
                All(
                    Not(Call("EvidenceConsistent", At(valuation, proposition))),
                    Not(entails))));

        Formula distinctFormulas = All(
            NotEqual(proposition, negatedProposition),
            NotEqual(conclusion, proposition),
            NotEqual(conclusion, negatedProposition));

        return Disp(ForAll(
            [
                Bound("Formula", type),
                Bound("proposition", formulaCarrier),
                Bound("negatedProposition", formulaCarrier),
                Bound("conclusion", formulaCarrier),
            ],
            Implies(
                distinctFormulas,
                Seq(
                    Let(entails, propositionType, entailmentDefinition),
                    witness))));
    }

    private static Formula Let(Formula name, Formula domain, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, name, Colon, Sp, domain, Sp,
            Eq, Sp, value, Comma, Sp);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Not(Formula value) => new Formula.Not(value);

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

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
