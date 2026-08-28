using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionLaws;

internal sealed class ObservationInterventionKernelStrictnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionLaws/"
            + "ObservationInterventionKernelStrictness."
            + "intervention_kernel_strictly_finer_than_observation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The intervention kernel is already strictly finer than the observational kernel on finite Boolean structural models.",
        H("Observation-Intervention Kernel Strictness"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-boolean-observation-intervention-kernel-strictness"),
            DeclarationHandle.Create(Declaration),
            H("The first causal-kernel inclusion is strict"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The intervention profile is constructed from the frozen finite Boolean "
                        + "structural-model channels. Its null action is exactly the observational "
                        + "response, while each nonnull action imposes one Boolean X value.")),
                Paragraph(Text(
                    "Equality of complete intervention profiles therefore forces observational "
                        + "equality by evaluation at the null action.")),
                Paragraph(Text(
                    "The frozen opposite-direction models have the same observational response "
                        + "but distinct imposed-X responses. Their pair belongs to the observational "
                        + "kernel and not the intervention kernel, making the inclusion strict."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula model = F.Id("M");
        Formula action = F.Id("a");
        Formula unit = F.Id("u");
        Formula imposedX = F.Id("x");
        Formula boolType = F.Id("Bool");
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula profile = F.Id("IntProfile");
        Formula profileType = Arrow(
            modelType,
            Arrow(Call("Option", boolType), Arrow(boolType, Product(boolType, boolType))));
        Formula profileConstruction = Call(
            "optionCases",
            action,
            Call("Obs", model, unit),
            Seq(LambdaLower, Sp, imposedX, Comma, Sp, Call("Int", model, imposedX, unit)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            profile, Sp, Colon, Sp, profileType, Comma, RowBreak, Grp(),
            profile, Open, model, Comma, Sp, action, Comma, Sp, unit, Close,
            Sp, Colon, Eq, Sp, profileConstruction, Comma, RowBreak, Grp(),
            Call("StrictSubset", Call("ker", profile), Call("ker", F.Id("Obs"))), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);
}
