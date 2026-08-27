using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class SelfConstraintMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Agency/SelfConstraintMonotonicity."
            + "appended_record_shrinks_consistent_actions";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appending one ledger record can only shrink the actions consistent with every record.",
        H("Self-Constraint Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("an-appended-record-shrinks-the-consistent-action-set"),
            DeclarationHandle.Create(Declaration),
            H("An appended record shrinks the consistent action set"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A state-indexed relation says whether a candidate action is consistent "
                        + "with one ledger record. The old and new admissible action sets are "
                        + "constructed directly by requiring this relation for every record in "
                        + "the old ledger and in its one-record extension.")),
                Paragraph(Text(
                    "Every old record remains a member after the append. Therefore an action "
                        + "satisfying every constraint in the extended ledger satisfies every "
                        + "constraint in the old ledger."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula ConsistentActions(
        Formula actionType,
        Formula ledger,
        Formula consistent,
        Formula state)
    {
        Formula action = F.Id("a");
        Formula record = F.Id("r");
        return Seq(
            OpenBrace, action, Colon, Sp, actionType, Sp, Mid, Sp,
            Forall, Sp, record, Sp, InMacro, Sp, ledger, Comma, Sp,
            Call("consistent", state, record, action), CloseBrace);
    }

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("State"), recordType = F.Id("Record");
        Formula actionType = F.Id("Action"), type = F.Id("Type");
        Formula consistent = F.Id("consistent"), state = F.Id("x");
        Formula oldLedger = F.Id("L"), newRecord = F.Id("q");
        Formula proposition = F.Id("Prop");
        Formula consistentType = Arrow(
            stateType, Arrow(recordType, Arrow(actionType, proposition)));
        Formula listType = Call("List", recordType);
        Formula extendedLedger = Call(
            "append", oldLedger, Call("singleton", newRecord));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("State"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("Record"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("Action"), type),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("consistent"), consistentType),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), stateType),
                new Formula.BoundVariable(FormulaIdentifier.Create("L"), listType),
                new Formula.BoundVariable(FormulaIdentifier.Create("q"), recordType),
            ],
            new Formula.Relation(
                ConsistentActions(actionType, extendedLedger, consistent, state),
                FormulaRelationOperator.SubsetOf,
                ConsistentActions(actionType, oldLedger, consistent, state))));
    }
}
