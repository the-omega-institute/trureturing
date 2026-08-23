using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class BranchingFreedomNeedsRelationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A process with two distinct futures is not functional, and branching autonomy "
            + "strictly strengthens autonomy.",
        H("Branching Freedom Needs a Relation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("branching-process-is-not-functional"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "branching_process_is_not_functional"),
                H("A branching process is not functional"),
                StatementSource.FromAuthor(BranchingProcessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A branch supplies one state with two distinct possible successors. "
                            + "If the process were the graph of a deterministic function, "
                            + "membership in the corresponding singleton would identify both "
                            + "successors with the same function value.")),
                    Paragraph(Text(
                        "The two successors would then be equal, contradicting the branch. "
                            + "Thus a genuinely branching transition process cannot be "
                            + "represented by any state-transition function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("functional-process-is-not-branching"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "functional_process_is_not_branching"),
                H("A functional process has no branch"),
                StatementSource.FromAuthor(FunctionalProcessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The process induced by a function assigns each state the singleton "
                        + "containing its function value. Any two possible successors of the "
                        + "same state must therefore coincide, so no pair of distinct futures "
                        + "can witness branching."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("branching-freedom-strictly-strengthens-autonomy"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "branching_freedom_strictly_stronger_than_autonomy"),
                H("Branching freedom strictly strengthens autonomy"),
                StatementSource.FromAuthor(StrictStrengthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Branching autonomy includes autonomy as one of its conditions, so "
                            + "every branching-autonomous process family is insensitive to at "
                            + "least two distinct external inputs.")),
                    Paragraph(Text(
                        "The converse fails for the Boolean identity process, chosen "
                            + "independently of the external input. False and true give the "
                            + "same transition relation, establishing autonomy, but every state "
                            + "has only its singleton identity successor, so the family has no "
                            + "branch under any input."))),
                DescribeRole.Lemma))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula SetOf(Formula carrier) =>
        Call("Set", carrier);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Singleton(Formula element) =>
        new Formula.SetLiteral([element]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula BranchingProcessFormula()
    {
        Formula state = F.Id("X");
        Formula process = F.Id("F");
        Formula function = F.Id("f");
        Formula point = F.Id("a");
        Formula processType = Arrow(state, SetOf(state));
        Formula functionType = Arrow(state, state);
        Formula functionalRepresentation = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("f", functionType)],
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("a", state)],
                Equal(
                    Apply(process, point),
                    Singleton(Apply(function, point)))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("X", TypeUniverse()), Bound("F", processType)],
            new Formula.Logic(
                Call("BranchingFree", process),
                FormulaLogicOperator.Implies,
                new Formula.Not(functionalRepresentation))));
    }

    private static Formula FunctionalProcessFormula()
    {
        Formula state = F.Id("X");
        Formula function = F.Id("f");
        Formula point = F.Id("a");
        Formula singletonProcess = Seq(
            point,
            Sp,
            Mapsto,
            Sp,
            Singleton(Apply(function, point)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("f", Arrow(state, state)),
            ],
            new Formula.Not(Call("BranchingFree", singletonProcess))));
    }

    private static Formula StrictStrengthFormula()
    {
        Formula external = F.Id("External");
        Formula state = F.Id("X");
        Formula processFamily = F.Id("P");
        Formula boolean = F.Id("Bool");
        Formula processFamilyType = Arrow(external, Arrow(state, SetOf(state)));
        Formula booleanProcessFamilyType =
            Arrow(boolean, Arrow(boolean, SetOf(boolean)));
        Formula implication = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("External", TypeUniverse()),
                Bound("X", TypeUniverse()),
                Bound("P", processFamilyType),
            ],
            new Formula.Logic(
                Call("BranchingAutonomousFree", processFamily),
                FormulaLogicOperator.Implies,
                Call("AutonomousFree", processFamily)));
        Formula strictWitness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("P", booleanProcessFamilyType)],
            new Formula.Logic(
                Call("AutonomousFree", processFamily),
                FormulaLogicOperator.And,
                new Formula.Not(Call("BranchingAutonomousFree", processFamily))));

        return Disp(new Formula.Logic(
            implication,
            FormulaLogicOperator.And,
            strictWitness));
    }
}
