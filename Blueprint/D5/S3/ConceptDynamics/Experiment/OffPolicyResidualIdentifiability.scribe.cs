using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class OffPolicyResidualIdentifiabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Behavior laws identify a target policy exactly when no model pair remains ambiguous.",
        H("Off-Policy Residual Identifiability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "target-policy-identifiable-iff-off-policy-residual-empty"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Experiment/"
                        + "OffPolicyResidualIdentifiability."
                        + "target_policy_identifiable_iff_off_policy_residual_empty"),
                H("An empty off-policy residual characterizes identifiability"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A behavior law and a target-policy law are readouts on the same "
                            + "model class. Identifiability means that any two models with "
                            + "the same behavior law have the same target-policy law.")),
                    Paragraph(Text(
                        "The off-policy residual consists exactly of model pairs with equal "
                            + "behavior laws and unequal target-policy laws. Fiber constancy "
                            + "is therefore equivalent to emptiness of this residual, "
                            + "including for an empty model class."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula behavior = F.Id("behaviorLaw");
        Formula target = F.Id("targetPolicyLaw");
        Formula identifiable = Call(
            "IdentifiableFromBehaviorLaw", behavior, target);
        Formula residualEmpty = new Formula.Relation(
            Call("offPolicyResidual", behavior, target),
            FormulaRelationOperator.Equal,
            F.Id("EmptySet"));

        return F.Disp(new Formula.Logic(
            identifiable,
            FormulaLogicOperator.Iff,
            residualEmpty));
    }
}
