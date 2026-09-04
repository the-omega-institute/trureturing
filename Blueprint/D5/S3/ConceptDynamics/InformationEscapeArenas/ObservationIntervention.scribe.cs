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
        Blocks(
            Definition("causal-direction-decidable-equality", "instDecidableEqCausalDirection",
                "Causal-direction decidable equality",
                "The decidable-equality instance is obtained by exhaustive constructor comparison."),
            Definition("causal-direction-finite", "instFintypeCausalDirection",
                "Finite causal directions",
                "The finite instance lists the two causal-direction constructors exhaustively."),
            Definition("scm-equivalence", "scmEquiv", "Boolean SCM equivalence",
                "The source models are equivalent to a direction paired with two unary Boolean tables."),
            Definition("scm-finite", "instFintypeDeterministicBoolSCM", "Finite Boolean SCMs",
                "The finite instance is obtained through a private equivalence."),
            Definition("scm-decidable-equality", "instDecidableEqDeterministicBoolSCM",
                "Boolean SCM decidable equality",
                "The decidable-equality instance is obtained through a private equivalence."),
            Definition("observation-readout", "ObservationReadout", "Observation readout indices",
                "The readout index type has one observational role and one interventional role."),
            Definition("observation-readout-finite", "instFintypeObservationReadout",
                "Finite observation readouts",
                "The finite instance lists the two readout constructors exhaustively."),
            Definition("observation-intervention-signature", "observationInterventionSignature",
                "Observation-intervention signature",
                "The signature assigns typed Boolean response tables to two CUT readout indices."),
            Definition("observation-intervention-statement", "ObservationInterventionStatement",
                "Frozen observation-intervention statement",
                "This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation.observation_strictly_weaker_than_intervention."),
            Definition("observation-intervention-arena", "observationInterventionArena",
                "Observation-intervention arena",
                "The law asks for two source models with equal observation CUTs and unequal intervention CUTs."),
            Describe.Lean(
                DescribeId.Create("observation-intervention-arena-nondegenerate"),
                DeclarationHandle.Create(Prefix + "observationInterventionArena_nondegenerate"),
                H("Observation-intervention arena is nondegenerate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Nondegenerate")), Open,
                    Operatorname, Grp(F.Id("toArena")), Open,
                    F.Id("observationInterventionArena"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite source carrier contains a pair of distinct models."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);
}
