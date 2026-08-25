using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class SharedSourceObservationDependenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Information/SharedSourceObservationDependence."
            + "shared_source_observations_are_not_independent";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two copies of one fair Boolean source agree surely but are not independent.",
        H("Shared Source Observation Dependence"),
        Blocks(Describe.Lean(
            DescribeId.Create("shared-source-observation-dependence"),
            DeclarationHandle.Create(Declaration),
            H("Shared fair-source observations are not independent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source law assigns mass one half to each Boolean state. Both "
                        + "observation channels copy that same source state.")),
                Paragraph(Text(
                    "Their equality event therefore has probability one. Each one-event "
                        + "has probability one half, so the marginal product is one quarter.")),
                Paragraph(Text(
                    "The joint one-event is the single true source state and has probability "
                        + "one half. Its mismatch with the marginal product is the explicit "
                        + "failure of independence."))),
            DescribeRole.Theorem))));

    private static Formula Probability(Formula eventFormula) =>
        Seq(F.Id("P"), Open, eventFormula, Close);

    private static Formula TheoremFormula()
    {
        Formula observationP = new Formula.Subscript(F.Id("X"), F.Id("p"));
        Formula observationQ = new Formula.Subscript(F.Id("X"), F.Id("q"));
        Formula pIsOne = Seq(observationP, Sp, Eq, Sp, D(1));
        Formula qIsOne = Seq(observationQ, Sp, Eq, Sp, D(1));
        Formula pMarginal = Probability(pIsOne);
        Formula qMarginal = Probability(qIsOne);
        Formula marginalProduct = Seq(pMarginal, Sp, qMarginal);
        Formula jointEvent = Probability(Seq(pIsOne, Sp, Land, Sp, qIsOne));
        Formula quarter = Seq(Frac, Grp(D(1)), Grp(D(4)));
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Probability(Seq(observationP, Sp, Eq, Sp, observationQ)),
            Sp, Eq, Sp, D(1), Sp, Land,
            RowBreak, Grp(),
            marginalProduct, Sp, Eq, Sp, quarter, Sp, Land,
            RowBreak, Grp(),
            marginalProduct, Sp, Neq, Sp, jointEvent, Sp, Land,
            RowBreak, Grp(),
            jointEvent, Sp, Eq, Sp, half, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
