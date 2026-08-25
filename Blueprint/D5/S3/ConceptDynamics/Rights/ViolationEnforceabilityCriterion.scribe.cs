using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Rights;

internal sealed class ViolationEnforceabilityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Rights/ViolationEnforceabilityCriterion."
            + "violation_enforceability_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact violation enforcement is equivalent to audit-interface sufficiency, while a "
            + "merged violation fiber forces an enforcement error.",
        H("Violation Enforceability Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("violation-enforceability-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Exact enforcement requires a violation-sufficient audit interface"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "On a nonempty event type, an exact Boolean enforcer exists precisely when "
                        + "the canonical effective violation target refines the audit log.")),
                Paragraph(Text(
                    "If two events have the same log value but different violation values, every "
                        + "enforcer restricted to that log value is wrong on at least one event.")),
                Paragraph(Text(
                    "The explicit Boolean countermodel has an identity violation target and a "
                        + "constant Unit-valued interface. It records a genuine violation "
                        + "distinction while proving that the interface is insufficient.")),
                Paragraph(Text(
                    "The nonempty-event premise is displayed because the canonical target image "
                        + "may otherwise be empty even though a raw Boolean executor exists."))),
            DescribeRole.Theorem))));

    private static Formula Concept(Formula state, Formula value) =>
        Call("Concept", state, value);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula eventType = F.Id("Gamma");
        Formula logType = F.Id("BLog");
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula auditLog = F.Id("L");
        Formula violation = F.Id("V");
        Formula enforcer = F.Id("e");
        Formula eventValue = F.Id("gamma");
        Formula otherEvent = F.Id("gammaPrime");
        Formula logReadout = Concept(eventType, logType);
        Formula violationReadout = Concept(eventType, boolean);
        Formula enforcerType = new Formula.TypeArrow(logType, boolean);
        Formula executorExists = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("e"),
            enforcerType,
            Seq(violation, Sp, Eq, Sp, enforcer, Sp, Circ, Sp, auditLog));
        Formula effectiveCriterion = Call(
            "Refines", Call("canonicalTargetReadout", violation), auditLog);
        Formula exactCriterion = new Formula.Logic(
            executorExists, FormulaLogicOperator.Iff, effectiveCriterion);
        Formula collision = And(
            Seq(Apply(auditLog, eventValue), Sp, Eq, Sp, Apply(auditLog, otherEvent)),
            Seq(Apply(violation, eventValue), Sp, Neq, Sp, Apply(violation, otherEvent)));
        Formula oneError = new Formula.Logic(
            Seq(
                Apply(enforcer, Apply(auditLog, eventValue)), Sp, Neq, Sp,
                Apply(violation, eventValue)),
            FormulaLogicOperator.Or,
            Seq(
                Apply(enforcer, Apply(auditLog, otherEvent)), Sp, Neq, Sp,
                Apply(violation, otherEvent)));
        Formula everyEnforcer = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("e"),
            enforcerType,
            oneError);
        Formula collisionLaw = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new(FormulaIdentifier.Create("gamma"), eventType),
                new(FormulaIdentifier.Create("gammaPrime"), eventType),
            ],
            Implies(collision, everyEnforcer));

        Formula declaredViolation = F.Id("Vzero");
        Formula interfaceReadout = F.Id("Lzero");
        Formula boolEvent = F.Id("b");
        Formula otherBoolEvent = F.Id("bPrime");
        Formula declaredType = Concept(boolean, boolean);
        Formula interfaceType = Concept(boolean, unit);
        Formula explicitCollision = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(FormulaIdentifier.Create("b"), boolean),
                new(FormulaIdentifier.Create("bPrime"), boolean),
            ],
            And(
                Seq(
                    Apply(interfaceReadout, boolEvent), Sp, Eq, Sp,
                    Apply(interfaceReadout, otherBoolEvent)),
                Seq(
                    Apply(declaredViolation, boolEvent), Sp, Neq, Sp,
                    Apply(declaredViolation, otherBoolEvent))));
        Formula interfaceGap = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(FormulaIdentifier.Create("Vzero"), declaredType),
                new(FormulaIdentifier.Create("Lzero"), interfaceType),
            ],
            And(
                explicitCollision,
                new Formula.Not(Call(
                    "Refines",
                    Call("canonicalTargetReadout", declaredViolation),
                    interfaceReadout))));
        Formula clauses = And(exactCriterion, And(collisionLaw, interfaceGap));
        Formula criterion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new(FormulaIdentifier.Create("Gamma"), type),
                new(FormulaIdentifier.Create("BLog"), type),
                new(FormulaIdentifier.Create("L"), logReadout),
                new(FormulaIdentifier.Create("V"), violationReadout),
            ],
            Implies(Call("Nonempty", eventType), clauses));

        return Disp(criterion);
    }
}
