using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionLaws;

internal sealed class SingleWorldPerfectInterventionLawDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionLaws/SingleWorldPerfectInterventionLaw."
            + "all_single_world_perfect_intervention_laws_agree";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stable and flip Boolean SCMs agree under every single-world perfect intervention.",
        H("Single-World Perfect-Intervention Laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("all-single-world-perfect-intervention-laws-agree"),
            DeclarationHandle.Create(Declaration),
            H("All single-world perfect-intervention laws agree"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The stable model returns the exogenous unit, while the flip model "
                        + "complements it exactly when the imposed treatment is true. The "
                        + "treatment-intervention marginal counts both values of the uniform "
                        + "exogenous unit.")),
                Paragraph(Text(
                    "A perfect intervention fixes either X or Y. The endogenous joint count "
                        + "law is constructed by evaluating the remaining structural equation "
                        + "over the four equally weighted pairs of independent Boolean "
                        + "exogenous coordinates.")),
                Paragraph(Text(
                    "The first public clause gives count one to each potential outcome in both "
                        + "models. The second compares the complete endogenous joint count law "
                        + "for every intervention, so interventions fixing Y are included."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula treatment = F.Id("x");
        Formula result = F.Id("y");
        Formula intervention = F.Id("a");
        Formula jointResult = F.Id("z");
        Formula stable = F.Id("S");
        Formula flip = F.Id("F");
        Formula boolType = F.Id("Bool");
        Formula interventionType = F.Id("PerfectIntervention");
        Formula stableMarginal = Equal(Call("Int", stable, treatment, result), D(1));
        Formula flipMarginal = Equal(Call("Int", flip, treatment, result), D(1));
        Formula sameJointLaw = Equal(
            Call("endogenousLaw", stable, intervention, jointResult),
            Call("endogenousLaw", flip, intervention, jointResult));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, Forall, Sp, treatment, Comma, Sp, result, Colon, Sp, boolType, Comma, Sp,
            stableMarginal, Sp, Land, Sp, flipMarginal, Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, Forall, Sp, intervention, Colon, Sp, interventionType, Comma, Sp,
            jointResult, Colon, Sp, boolType, Sp, Times, Sp, boolType, Comma, Sp,
            sameJointLaw, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
