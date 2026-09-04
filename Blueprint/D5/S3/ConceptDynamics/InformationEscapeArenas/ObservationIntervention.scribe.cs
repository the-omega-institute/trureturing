using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class ObservationInterventionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observation versus intervention is expressed by two typed CUT slots.",
        H("Observation Intervention Arena"),
        Blocks(Describe.Lean(
            DescribeId.Create("observation-intervention-arena"),
            DeclarationHandle.Create(Prefix + "observationInterventionArena"),
            H("Observation-intervention arena"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("observationInterventionArena"),
                Colon, Sp, F.Id("PrimitiveLawArena"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The law asks for two source models with equal observation CUTs and unequal intervention CUTs."))),
            DescribeRole.Definition))));
}
