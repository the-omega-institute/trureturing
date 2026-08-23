using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;

internal sealed class AnswerableTargetMonotonicityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Answering/AnswerableTargetMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every target answerable through a concept remains answerable through any refinement.",
        H("Answerable Targets Are Monotone under Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("answerable-targets-grow-under-concept-refinement"),
            DeclarationHandle.Create(DeclarationPrefix + "answerable_target_monotone"),
            H("Answerable targets grow under concept refinement"),
            StatementSource.FromAuthor(MonotonicityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A target belongs to the answerable set exactly when its canonical target "
                    + "readout factors through the concept. If the coarse concept itself "
                    + "factors through a finer concept, composing those two canonical "
                    + "refinement witnesses proves the required set inclusion."))),
            DescribeRole.Theorem))));

    private static Formula MonotonicityFormula()
    {
        Formula state = F.Id("X");
        Formula coarseCoordinate = F.Id("C");
        Formula fineCoordinate = F.Id("D");
        Formula target = F.Id("Y");
        Formula coarse = F.Id("qC");
        Formula fine = F.Id("qD");
        Formula arrow(Formula domain, Formula codomain) =>
            new Formula.TypeArrow(domain, codomain);
        Formula concept(Formula coordinate) => arrow(state, coordinate);
        Formula premise = Call("Refines", coarse, fine);
        Formula conclusion = new Formula.Relation(
            Call("AnswerableTargets", coarse, target),
            FormulaRelationOperator.SubsetOf,
            Call("AnswerableTargets", fine, target));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("C"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("D"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("qC"), concept(coarseCoordinate)),
                new Formula.BoundVariable(FormulaIdentifier.Create("qD"), concept(fineCoordinate)),
            ],
            new Formula.Logic(
                premise,
                FormulaLogicOperator.Implies,
                conclusion)));
    }
}
