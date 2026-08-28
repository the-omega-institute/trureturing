using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.LongitudinalCausal;

internal sealed class LongitudinalStructuralCausalModelDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite longitudinal policies preserve state mechanisms and expose feedback effects.",
        H("Longitudinal Structural Causal Model"),
        Blocks(
            Definition(
                "dynamic-policy",
                "dynamicPolicy",
                "Dynamic policy",
                "At each finite time, a dynamic policy maps the exact observed history to "
                    + "a probability mass function on actions."),
            Definition(
                "policy-intervention",
                "policyIntervention",
                "Policy intervention",
                "A policy intervention replaces the behavior assignment while preserving "
                    + "the initial law, state-transition mechanism, and outcome map."),
            Definition(
                "policy-result",
                "policyResult",
                "Policy result",
                "The policy result is the final outcome law after sequentially sampling every "
                    + "policy action and retained state transition."),
            Theorem(
                "static-intervention-is-length-one",
                "static_intervention_is_length_one",
                "Static intervention is the length-one case",
                StaticInterventionFormula(),
                "The constant policy embedding and the direct static intervention induce the "
                    + "same probability mass function on final outcomes."),
            Theorem(
                "feedback-is-necessary",
                "feedback_is_necessary",
                "Feedback changes a two-step result law",
                FeedbackFormula(),
                "In the Boolean witness, the first action becomes the next covariate and the "
                    + "second action reads it. The dynamic law is therefore distinct from the "
                    + "feedback-ignoring static result."),
            Theorem(
                "no-feedback-static-dynamic-agree",
                "no_feedback_static_dynamic_agree",
                "Removing feedback restores agreement",
                NoFeedbackFormula(),
                "In the matched two-step model with the action-to-state link removed, the "
                    + "dynamic and feedback-ignoring policy laws coincide."))));

    private static DocumentBlock.Describe Definition(
        string id,
        string declaration,
        string heading,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(DeclarationPrefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(DeclarationPrefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Theorem);

    private static Formula StaticInterventionFormula()
    {
        Formula model = F.Id("model");
        Formula action = F.Id("x");
        Formula embedded = new Formula.Apply(
            F.Id("staticPolicyEmbedding"), [action]);
        Formula dynamicLaw = new Formula.Apply(
            F.Id("policyResult"), [model, embedded]);
        Formula staticLaw = new Formula.Apply(
            F.Id("staticInterventionResult"), [model, action]);
        return Disp(new Formula.Relation(
            dynamicLaw, FormulaRelationOperator.Equal, staticLaw));
    }

    private static Formula FeedbackFormula()
    {
        Formula dynamicLaw = new Formula.Apply(
            F.Id("policyResult"), [F.Id("feedbackModel"), F.Id("feedbackPolicy")]);
        return Disp(new Formula.Relation(
            dynamicLaw,
            FormulaRelationOperator.NotEqual,
            F.Id("feedbackIgnoringStaticResult")));
    }

    private static Formula NoFeedbackFormula()
    {
        Formula model = F.Id("noFeedbackModel");
        Formula dynamicLaw = new Formula.Apply(
            F.Id("policyResult"), [model, F.Id("feedbackPolicy")]);
        Formula staticLaw = new Formula.Apply(
            F.Id("policyResult"), [model, F.Id("feedbackIgnoringPolicy")]);
        return Disp(new Formula.Relation(
            dynamicLaw, FormulaRelationOperator.Equal, staticLaw));
    }
}
