using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TargetRisk;

internal sealed class RobustSafetyModelMonotonicityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/TargetRisk/RobustSafetyModelMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enlarging the audited model family can only shrink the robust safe-action set.",
        H("Robust Safety Under Model Expansion"),
        Blocks(Describe.Lean(
            DescribeId.Create("model-expansion-shrinks-robust-safe-set"),
            DeclarationHandle.Create(
                DeclarationPrefix + "model_uncertainty_expansion_shrinks_safe_set"),
            H("Model expansion shrinks the robust safe set"),
            StatementSource.FromAuthor(MonotonicityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A safe action must keep the supplied risk below the threshold for every "
                    + "admitted model. Any action satisfying this condition for an expanded "
                    + "model family also satisfies it for the original subfamily."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula SafeActions(
        Formula actionType,
        Formula models,
        Formula risk,
        Formula threshold)
    {
        Formula action = F.Id("u");
        Formula model = F.Id("m");

        return Seq(
            OpenBrace,
            action, Colon, Sp, actionType, Sp, Mid, Sp,
            Forall, Sp, model, Sp, InMacro, Sp, models, Comma, Sp,
            Call("risk", model, action), Sp, Leq, Sp, threshold,
            CloseBrace);
    }

    private static Formula MonotonicityFormula()
    {
        Formula modelType = F.Id("Model");
        Formula actionType = F.Id("Action");
        Formula risk = F.Id("risk");
        Formula threshold = F.Id("alpha");
        Formula models = Seq(Mathcal, Grp(F.Id("M")));
        Formula expandedModels = Seq(Mathcal, Grp(F.Id("M")), Apos);
        Formula realNumbers = Seq(Mathbb, Grp(F.Id("R")));
        Formula modelSet = Call("Set", modelType);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, modelType, Comma, Sp, actionType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            risk, Colon, Sp,
            Arrow(modelType, Arrow(actionType, realNumbers)), Comma, Sp,
            threshold, Colon, Sp, realNumbers, Comma, RowBreak, Grp(),
            models, Comma, Sp, expandedModels, Colon, Sp, modelSet, Comma, RowBreak, Grp(),
            models, Sp, Subseteq, Sp, expandedModels, Sp, Rightarrow, Sp, RowBreak, Grp(),
            SafeActions(actionType, expandedModels, risk, threshold), Sp,
            Subseteq, Sp,
            SafeActions(actionType, models, risk, threshold), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
