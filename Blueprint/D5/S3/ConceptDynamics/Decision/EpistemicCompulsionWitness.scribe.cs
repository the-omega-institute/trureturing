using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class EpistemicCompulsionWitnessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Decision/EpistemicCompulsionWitness."
            + "epistemic_compulsion_witness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coarse observation can leave no action safe across its whole fiber.",
        H("Epistemic Compulsion Witness"),
        Blocks(Describe.Lean(
            DescribeId.Create("epistemic-compulsion-witness"),
            DeclarationHandle.Create(Declaration),
            H("Pointwise legality need not survive coarse observation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two Boolean states share one observation. An action is legal exactly "
                        + "when it matches the underlying state, so each state separately has a "
                        + "legal action.")),
                Paragraph(Text(
                    "Because the observation cannot distinguish false from true, no single "
                        + "Boolean action is legal throughout the common fiber. This is an "
                        + "explicit finite witness of epistemic compulsion."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula proposition = F.Id("Prop");
        Formula observation = F.Id("q");
        Formula legal = F.Id("Legal");
        Formula z = F.Id("z");
        Formula state = F.Id("x");
        Formula action = F.Id("a");
        Formula observationType = Arrow(boolean, unit);
        Formula legalType = Arrow(boolean, Arrow(boolean, proposition));
        Formula pointwiseLegal = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            boolean,
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("a"),
                boolean,
                Apply(Apply(legal, state), action)));
        Formula exactLegality = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), boolean),
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), boolean),
            ],
            new Formula.Logic(
                Apply(Apply(legal, state), action),
                FormulaLogicOperator.Iff,
                new Formula.Relation(action, FormulaRelationOperator.Equal, state)));
        Formula sameObservation = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            boolean,
            new Formula.Relation(
                Apply(observation, state),
                FormulaRelationOperator.Equal,
                z));
        Formula commonSafeAction = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("a"),
            boolean,
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"),
                boolean,
                new Formula.Logic(
                    new Formula.Relation(
                        Apply(observation, state),
                        FormulaRelationOperator.Equal,
                        z),
                    FormulaLogicOperator.Implies,
                    Apply(Apply(legal, state), action))));
        Formula clauses = And(
            pointwiseLegal,
            And(exactLegality, And(sameObservation, new Formula.Not(commonSafeAction))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("q"), observationType),
                new Formula.BoundVariable(FormulaIdentifier.Create("Legal"), legalType),
                new Formula.BoundVariable(FormulaIdentifier.Create("z"), unit),
            ],
            clauses));
    }
}
