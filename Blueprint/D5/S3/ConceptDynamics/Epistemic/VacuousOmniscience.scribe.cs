using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class VacuousOmniscienceDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Epistemic/VacuousOmniscience.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Empty evidence fibers induce vacuous omniscience, while fiber witnesses prevent "
            + "the collapse and robust knowledge supplies such a witness.",
        H("Vacuous Omniscience"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("empty-fiber-knows-everything"),
                DeclarationHandle.Create(DeclarationPrefix + "empty_fiber_knows_everything"),
                H("An empty evidence fiber knows every predicate"),
                StatementSource.FromAuthor(EmptyFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The admissible evidence fiber over b consists of the admissible "
                            + "states whose evidence equals b. If this fiber is empty, there "
                            + "is no state at which a candidate predicate can fail the "
                            + "fiberwise knowledge condition.")),
                    Paragraph(Text(
                        "Consequently every state predicate is fiberwise known at b. This is "
                            + "the vacuous-omniscience collapse caused by asking for universal "
                            + "agreement over an empty collection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonempty-fiber-excludes-vacuous-omniscience"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nonempty_fiber_excludes_vacuous_omniscience"),
                H("A fiber witness excludes vacuous omniscience"),
                StatementSource.FromAuthor(NonemptyFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A state in the admissible evidence fiber prevents all predicates from "
                        + "being known there. The constantly false predicate fails at that "
                        + "witness, so it provides a specific predicate whose fiberwise "
                        + "knowledge assertion is false."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("robust-knowledge-supplies-fiber-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "robust_knowledge_supplies_fiber_witness"),
                H("Robust knowledge supplies a fiber witness"),
                StatementSource.FromAuthor(RobustKnowledgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Robust knowledge requires its anchor to be admissible. The anchor also "
                        + "has the same evidence as itself, so it lies in its own admissible "
                        + "evidence fiber and witnesses that the fiber is nonempty."))),
                DescribeRole.Lemma))));

    private static Formula.TypeArrow Arrow(Formula domain, Formula codomain) =>
        new(domain, codomain);

    private static Formula.Logic And(Formula left, Formula right) =>
        new(left, FormulaLogicOperator.And, right);

    private static Formula.Logic ImpliesFormula(Formula left, Formula right) =>
        new(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula FiberKnowledge(
        Formula admissible,
        Formula evidence,
        Formula fiber,
        Formula predicate) =>
        Call("fiberKnowledge", admissible, evidence, fiber, predicate);

    private static Formula RobustKnowledge(
        Formula admissible,
        Formula evidence,
        Formula predicate,
        Formula anchor) =>
        Call("robustKnowledge", admissible, evidence, predicate, anchor);

    private static Formula EmptyFiberFormula()
    {
        Formula stateType = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula proposition = F.Id("Prop");
        Formula admissible = F.Id("A");
        Formula evidence = F.Id("e");
        Formula fiber = F.Id("b");
        Formula state = F.Id("x");
        Formula predicate = F.Id("P");
        Formula emptyFiber = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            stateType,
            ImpliesFormula(
                Apply(admissible, state),
                new Formula.Not(Equal(Apply(evidence, state), fiber))));
        Formula everyPredicate = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("P"),
            Arrow(stateType, proposition),
            FiberKnowledge(admissible, evidence, fiber, predicate));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("B", F.Id("Type")),
                Bound("A", Arrow(stateType, proposition)),
                Bound("e", Arrow(stateType, evidenceType)),
                Bound("b", evidenceType),
            ],
            ImpliesFormula(emptyFiber, everyPredicate)));
    }

    private static Formula NonemptyFiberFormula()
    {
        Formula stateType = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula proposition = F.Id("Prop");
        Formula admissible = F.Id("A");
        Formula evidence = F.Id("e");
        Formula fiber = F.Id("b");
        Formula state = F.Id("x");
        Formula predicate = F.Id("P");
        Formula fiberWitness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("x"),
            stateType,
            And(
                Apply(admissible, state),
                Equal(Apply(evidence, state), fiber)));
        Formula excludedPredicate = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("P"),
            Arrow(stateType, proposition),
            new Formula.Not(FiberKnowledge(admissible, evidence, fiber, predicate)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("B", F.Id("Type")),
                Bound("A", Arrow(stateType, proposition)),
                Bound("e", Arrow(stateType, evidenceType)),
                Bound("b", evidenceType),
            ],
            ImpliesFormula(fiberWitness, excludedPredicate)));
    }

    private static Formula RobustKnowledgeFormula()
    {
        Formula stateType = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula proposition = F.Id("Prop");
        Formula admissible = F.Id("A");
        Formula evidence = F.Id("e");
        Formula predicate = F.Id("P");
        Formula anchor = F.Id("a");
        Formula state = F.Id("x");
        Formula fiberWitness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("x"),
            stateType,
            And(
                Apply(admissible, state),
                Equal(Apply(evidence, state), Apply(evidence, anchor))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("B", F.Id("Type")),
                Bound("A", Arrow(stateType, proposition)),
                Bound("e", Arrow(stateType, evidenceType)),
                Bound("P", Arrow(stateType, proposition)),
                Bound("a", stateType),
            ],
            ImpliesFormula(
                RobustKnowledge(admissible, evidence, predicate, anchor),
                fiberWitness)));
    }
}
