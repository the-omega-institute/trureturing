using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Aggregation;

internal sealed class IndividualRationalityMajorityCycleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Aggregation/IndividualRationalityMajorityCycle."
            + "individual_rationality_majority_cycle";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete transitive individual rankings can aggregate into a nontransitive "
            + "majority cycle with no faithful scalar order.",
        H("Individual Rationality and Majority Cycles"),
        Blocks(Describe.Lean(
            DescribeId.Create("individual-rationality-produces-a-majority-cycle"),
            DeclarationHandle.Create(Declaration),
            H("Individually rational rankings produce a collective cycle"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The fixed profile ranks the three candidates cyclically across three "
                        + "voters. Every individual strict preference is transitive and "
                        + "complete on distinct candidates.")),
                Paragraph(Text(
                    "Pairwise counting makes zero beat one, one beat two, and two beat zero. "
                        + "Those public edges directly contradict transitivity of the majority "
                        + "relation, and the imported cycle obstruction excludes every faithful "
                        + "real-valued ordering."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Parenthesize(Formula formula) => Seq(Open, formula, Close);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula candidate = Call("Fin", Num(3));
        Formula voter = F.Id("v");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula utility = F.Id("u");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula prefers(Formula a, Formula b, Formula c) => Call("prefers", a, b, c);
        Formula majority(Formula a, Formula b) => Call("majorityPrefers", a, b);

        Formula individualTransitivity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("v", candidate), Bound("x", candidate), Bound("y", candidate), Bound("z", candidate)],
            Implies(
                And(prefers(voter, x, y), prefers(voter, y, z)),
                prefers(voter, x, z)));
        Formula individualCompleteness = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("v", candidate), Bound("x", candidate), Bound("y", candidate)],
            Implies(
                new Formula.Not(Equal(x, y)),
                new Formula.Logic(
                    prefers(voter, x, y),
                    FormulaLogicOperator.Or,
                    prefers(voter, y, x))));
        Formula cycle = And(
            majority(Num(0), Num(1)),
            And(majority(Num(1), Num(2)), majority(Num(2), Num(0))));
        Formula represents = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", candidate), Bound("y", candidate)],
            Implies(
                majority(x, y),
                new Formula.Relation(
                    Apply(utility, x),
                    FormulaRelationOperator.GreaterThan,
                    Apply(utility, y))));
        Formula scalarRepresentation = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("u"),
            Arrow(candidate, real),
            represents);

        return Disp(And(
            Parenthesize(individualTransitivity),
            And(
                Parenthesize(individualCompleteness),
                And(
                    cycle,
                    And(
                        new Formula.Not(Call("Transitive", F.Id("majorityPrefers"))),
                        new Formula.Not(scalarRepresentation))))));
    }
}
