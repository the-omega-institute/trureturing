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
            Definition("observation-intervention-concrete-realization",
                "observationInterventionRealization", "Concrete observation-intervention realization",
                "The primitive realization assigns the source observation and intervention functions to the two typed CUT slots."),
            Node("observation-intervention-realization",
                "observation_strictly_weaker_than_intervention_realization",
                "Observation-intervention realization",
                CertificateFormula(),
                "The equivalence preserves the existential model witnesses in both directions."),
            Node("observation-intervention-partition-count",
                "observation_strictly_weaker_than_intervention_partition_count",
                "Twenty-four kernel classes",
                PartitionCountFormula(),
                "Exhaustive evaluation of all 32 source models yields 24 joint signatures."),
            Node("observation-intervention-private-pair",
                "observation_strictly_weaker_than_intervention_private_pair",
                "Private pair separation",
                AgreesFormula(),
                "The named opposite-direction models disagree under intervention."))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);

    private static Formula CertificateFormula()
    {
        Formula modelM = F.Id("M");
        Formula modelN = F.Id("N");
        Formula carrier = F.Id("DeterministicBoolSCM");
        Formula witnesses = Seq(
            Exists, Sp, modelM, Comma, Sp, modelN, Colon, Sp, carrier, Comma, Sp,
            Apply(F.Id("Obs"), modelM), Sp, Eq, Sp, Apply(F.Id("Obs"), modelN),
            Sp, Land, Sp,
            Apply(F.Id("Int"), modelM), Sp, Neq, Sp, Apply(F.Id("Int"), modelN));
        Formula law = Seq(F.Id("observationInterventionArena"), Dot, F.Id("Law"),
            Open, F.Id("observationInterventionRealization"), Close);
        return Seq(Grp(witnesses), Sp, Iff, Sp, law);
    }

    private static Formula PartitionCountFormula()
    {
        Formula model = F.Id("model");
        Formula carrier = F.Id("DeterministicBoolSCM");
        Formula signature = Seq(Open, Apply(F.Id("Obs"), model), Comma, Sp,
            Apply(F.Id("Int"), model), Close);
        Formula imageCard = Seq(Open, F.Id("Finset"), Dot, F.Id("univ"), Dot,
            F.Id("image"), Open, Lambda(Seq(model, Colon, Sp, carrier), signature), Close,
            Close, Dot, F.Id("card"));
        return Seq(imageCard, Sp, Eq, Sp, D(2, 4));
    }

    private static Formula AgreesFormula() => Seq(
        Neg, Sp, F.Id("observationInterventionRealization"), Dot,
        F.Id("toPrimitiveBundle"), Dot, F.Id("agrees"), Open,
        F.Id("xCausesYModel"), Comma, Sp, F.Id("yCausesXModel"), Close);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);
}
