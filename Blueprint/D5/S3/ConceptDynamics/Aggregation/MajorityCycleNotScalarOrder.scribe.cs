using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Aggregation;

internal sealed class MajorityCycleNotScalarOrderDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete three-voter majority cycle cannot be faithfully represented by any "
            + "scalar linear order.",
        H("Majority Cycle Is Not a Scalar Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-directed-three-cycle-has-no-scalar-representation"),
                DeclarationHandle.Create(DeclarationPrefix + "three_cycle_not_scalar_order"),
                H("A directed three-cycle has no scalar representation"),
                StatementSource.FromAuthor(ThreeCycleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose a relation contains the directed edges a over b, b over c, and "
                        + "c over a. A faithful scalar representation would place u(a) above "
                        + "u(b), u(b) above u(c), and u(c) above u(a). Transitivity gives the "
                        + "opposite of the last strict inequality, so no map into a linear "
                        + "order can represent all three edges."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("each-condorcet-cycle-edge-wins-by-two-votes"),
                DeclarationHandle.Create(DeclarationPrefix + "condorcet_cycle_vote_counts"),
                H("Each Condorcet-cycle edge wins by two votes"),
                StatementSource.FromAuthor(CondorcetVoteCountsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three cyclic ballots rank the candidates as 0 over 1 over 2, 1 over "
                        + "2 over 0, and 2 over 0 over 1. Consequently exactly two voters prefer "
                        + "0 to 1, exactly two prefer 1 to 2, and exactly two prefer 2 to 0. "
                        + "These counts exhibit the three directed majority edges."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("the-majority-cycle-has-no-scalar-order"),
                DeclarationHandle.Create(DeclarationPrefix + "majority_cycle_not_scalar_order"),
                H("The majority cycle has no scalar order"),
                StatementSource.FromAuthor(MajorityCycleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Requiring two of the three voters makes 0 beat 1, 1 beat 2, and 2 "
                            + "beat 0. Thus the concrete majority relation contains the directed "
                            + "cycle certified by the vote-count lemma.")),
                    Paragraph(Text(
                        "Applying the abstract cycle obstruction shows that no assignment of "
                            + "utilities in any linear order can put every majority winner "
                            + "strictly above the candidate it defeats."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula GreaterThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ThreeCycleFormula()
    {
        Formula candidateType = F.Id("C");
        Formula utilityType = F.Id("U");
        Formula relation = F.Id("R");
        Formula first = F.Id("a");
        Formula second = F.Id("b");
        Formula third = F.Id("c");
        Formula utility = F.Id("u");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula cycle = And(
            Apply(relation, first, second),
            And(Apply(relation, second, third), Apply(relation, third, first)));
        Formula represents = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", candidateType), Bound("y", candidateType)],
            ImpliesFormula(
                Apply(relation, x, y),
                GreaterThan(Apply(utility, x), Apply(utility, y))));
        Formula representation = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("u"),
            Arrow(candidateType, utilityType),
            represents);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("C", F.Id("Type")),
                Bound("U", F.Id("Type")),
                Bound("o", Call("LinearOrder", utilityType)),
                Bound("R", Arrow(candidateType, Arrow(candidateType, F.Id("Prop")))),
                Bound("a", candidateType),
                Bound("b", candidateType),
                Bound("c", candidateType),
            ],
            ImpliesFormula(cycle, new Formula.Not(representation))));
    }

    private static Formula CondorcetVoteCountsFormula()
    {
        Formula votes(Formula winner, Formula loser) => Call("votes", winner, loser);
        Formula two = Num(2);

        return Disp(And(
            Equal(votes(Num(0), Num(1)), two),
            And(
                Equal(votes(Num(1), Num(2)), two),
                Equal(votes(Num(2), Num(0)), two))));
    }

    private static Formula MajorityCycleFormula()
    {
        Formula candidateType = Call("Fin", Num(3));
        Formula utilityType = F.Id("U");
        Formula utility = F.Id("u");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula represents = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", candidateType), Bound("y", candidateType)],
            ImpliesFormula(
                Call("majorityPrefers", x, y),
                GreaterThan(Apply(utility, x), Apply(utility, y))));
        Formula representation = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("u"),
            Arrow(candidateType, utilityType),
            represents);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("U", F.Id("Type")),
                Bound("o", Call("LinearOrder", utilityType)),
            ],
            new Formula.Not(representation)));
    }
}
