using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Discussion;

internal sealed class BoundedDiscussionBlindSpotPersistenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Discussion/BoundedDiscussionBlindSpotPersistence."
            + "bounded_discussion_cannot_remove_joint_blind_spot";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A discussion that only recombines the agents' joint information cannot resolve a "
            + "target blind spot of that information.",
        H("Bounded Discussion Blind-Spot Persistence"),
        Blocks(Describe.Lean(
            DescribeId.Create("bounded-discussion-preserves-a-joint-blind-spot"),
            DeclarationHandle.Create(Declaration),
            H("Joint blind spots survive bounded discussion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take two concept readouts and an indexed family of discussion messages. "
                        + "If the canonical target readout does not factor through the agents' "
                        + "joint readout, while every message does factor through it, then the "
                        + "target still does not factor through the join of the agents' readout "
                        + "with all messages.")),
                Paragraph(Text(
                    "The indexed message product remains bounded by the original joint readout. "
                        + "Its further join is therefore also bounded by that readout, so target "
                        + "factorization through the extended discussion would contradict the "
                        + "initial blind spot."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula leftValue = F.Id("B1");
        Formula rightValue = F.Id("B2");
        Formula targetValue = F.Id("Y");
        Formula messageValue = F.Id("BM");
        Formula left = F.Id("C1");
        Formula right = F.Id("C2");
        Formula message = F.Id("M");
        Formula target = F.Id("T");
        Formula index = F.Id("n");
        Formula common = Call("conceptJoin", left, right);
        Formula targetConcept = Call("canonicalTargetReadout", target);
        Formula messageFamilyType = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            indexType,
            Arrow(stateType, Apply(messageValue, index)));
        Formula initialBlindSpot = new Formula.Not(
            Call("Refines", targetConcept, common));
        Formula everyMessageBound = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            indexType,
            Call("Refines", Apply(message, index), common));
        Formula extendedDiscussion = Call(
            "conceptJoin", common, Call("jointReadout", message));
        Formula conclusion = new Formula.Not(
            Call("Refines", targetConcept, extendedDiscussion));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type),
                Bound("X", type),
                Bound("B1", type),
                Bound("B2", type),
                Bound("Y", type),
                Bound("BM", Arrow(indexType, type)),
                Bound("C1", Arrow(stateType, leftValue)),
                Bound("C2", Arrow(stateType, rightValue)),
                Bound("M", messageFamilyType),
                Bound("T", Arrow(stateType, targetValue)),
            ],
            Implies(And(initialBlindSpot, everyMessageBound), conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
