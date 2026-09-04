using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class ObservationInterventionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen observation-intervention theorem realizes a 24-class two-CUT kernel.",
        H("Observation Intervention Realization"),
        Blocks(
            Node("observation-intervention-realization",
                "observation_strictly_weaker_than_intervention_realization",
                "Observation-intervention realization",
                Call("LegacyPrimitiveRealization", F.Id("observationInterventionArena"),
                    F.Id("ObservationInterventionStatement"),
                    F.Id("observationInterventionRealization")),
                "The equivalence preserves the existential model witnesses in both directions."),
            Node("observation-intervention-partition-count",
                "observation_strictly_weaker_than_intervention_partition_count",
                "Twenty-four kernel classes",
                Seq(Call("card", F.Id("signatureClasses")), Sp, Eq, Sp, D(2, 4)),
                "Exhaustive evaluation of all 32 source models yields 24 joint signatures."),
            Node("observation-intervention-private-pair",
                "observation_strictly_weaker_than_intervention_private_pair",
                "Private pair separation",
                Call("Not", Call("agrees", F.Id("observationInterventionRealization"),
                    F.Id("xCausesYModel"), F.Id("yCausesXModel"))),
                "The named opposite-direction models disagree under intervention."))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);
}
