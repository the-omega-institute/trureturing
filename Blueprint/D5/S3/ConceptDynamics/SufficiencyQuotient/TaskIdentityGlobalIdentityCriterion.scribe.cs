using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SufficiencyQuotient;

internal sealed class TaskIdentityGlobalIdentityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/SufficiencyQuotient/TaskIdentityGlobalIdentityCriterion."
            + "task_identity_global_identity_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The target-profile quotient is the operational identity, and it becomes "
            + "global identity exactly for a jointly faithful target family.",
        H("Task Identity and Global Identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("task-identity-global-identity-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Task identity equals global identity exactly under joint faithfulness"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The target family is assembled by the canonical dependent joint readout. "
                        + "Its kernel quotient is exposed through the canonical class map, so "
                        + "two states have the same task identity exactly when every target "
                        + "returns the same value on them.")),
                Paragraph(Text(
                    "The joint readout is injective exactly when its kernel is equality. The "
                        + "same condition makes the quotient class map injective, which is the "
                        + "precise sense in which task identity then agrees with global identity.")),
                Paragraph(Text(
                    "A constant target family on Bool gives two distinct states with equal "
                        + "target values and equal quotient classes, making the separation "
                        + "clause substantive."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula outputFamily = F.Id("Y");
        Formula targets = F.Id("K");
        Formula index = F.Id("i");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula profile = Call("jointReadout", targets);
        Formula taskIdentity = Call("quotientClassMap", profile);
        Formula targetType = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Arrow(stateType, Apply(outputFamily, index)));
        Formula sameTargets = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Equal(
                Apply(Apply(targets, index), left),
                Apply(Apply(targets, index), right)));
        Formula sameTaskIdentity = Equal(
            Apply(taskIdentity, left), Apply(taskIdentity, right));
        Formula taskCriterion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", stateType), Bound("y", stateType)],
            IffFormula(sameTaskIdentity, sameTargets));
        Formula faithfulKernel = IffFormula(
            Call("Injective", profile),
            Equal(Call("ker", profile), Call("Eq", stateType)));
        Formula globalCriterion = IffFormula(
            Call("Injective", taskIdentity), Call("Injective", profile));
        Formula generalClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type), Bound("X", type),
                Bound("Y", Arrow(indexType, type)),
                Bound("K", targetType),
            ],
            And(taskCriterion, And(faithfulKernel, globalCriterion)));

        Formula unit = F.Id("Unit");
        Formula boolean = F.Id("Bool");
        Formula constantFamily = F.Id("q");
        Formula constantIndex = F.Id("j");
        Formula constantProfile = Call("jointReadout", constantFamily);
        Formula constantIdentity = Call("quotientClassMap", constantProfile);
        Formula constantFamilyType = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", unit)],
            Arrow(boolean, unit));
        Formula constantAgreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", unit)],
            Equal(
                Apply(Apply(constantFamily, constantIndex), left),
                Apply(Apply(constantFamily, constantIndex), right)));
        Formula counterexampleBody = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", boolean), Bound("y", boolean)],
            And(
                NotEqual(left, right),
                And(
                    constantAgreement,
                    Equal(Apply(constantIdentity, left), Apply(constantIdentity, right)))));
        Formula counterexample = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("q", constantFamilyType)],
            counterexampleBody);

        return F.Disp(And(generalClause, counterexample));
    }
}
