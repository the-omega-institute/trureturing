using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class SettleStopInputConservationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/"
            + "SettleStopInputConservation."
            + "settle_stop_depends_only_on_decision_and_orientation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stop component of settlement is conserved by equal decision and orientation inputs.",
        H("Settle Stop Input Conservation"),
        Blocks(Describe.Lean(
            DescribeId.Create("settle-stop-input-conservation"),
            DeclarationHandle.Create(Declaration),
            H("Settlement stop depends only on the sealed decision and orientation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two commitments have the same round and the same canonical "
                        + "prospective-commitment type. The two sourced orientations also "
                        + "share one orientation type and its admissible target and scope.")),
                Paragraph(Text(
                    "Under the decidable premises carried by the frozen finite checker, "
                        + "equality of the sealed decision fields and orientations preserves "
                        + "the Boolean settlement stop result."))),
            DescribeRole.Theorem))));

    private static Formula DecisionOf(Formula commitment) =>
        Call("decision", commitment);

    private static Formula SettlementOf(
        Formula admissible,
        Formula scope,
        Formula orientation,
        Formula commitment) =>
        Call("settleStop", admissible, scope, orientation, commitment);

    private static Formula TheoremFormula()
    {
        Formula round = F.Id("n");
        Formula commitment = F.Id("K");
        Formula commitmentPrime = F.Id("KPrime");
        Formula orientation = F.Id("O");
        Formula orientationPrime = F.Id("OPrime");
        Formula admissible = F.Id("AdmTarget");
        Formula scope = F.Id("InScope");
        Formula commitmentType = Call("ProspectiveCommitment", round);
        Formula orientationType = Call("OrientationSpec", admissible, scope);
        Formula equalInputs = Seq(
            Open,
            DecisionOf(commitment), Sp, Eq, Sp, DecisionOf(commitmentPrime),
            Sp, Land, Sp,
            orientation, Sp, Eq, Sp, orientationPrime,
            Close);

        return Disp(Seq(
            Forall, Sp,
            commitment, Comma, Sp, commitmentPrime, Colon, Sp, commitmentType,
            Comma, RowBreak, Grp(),
            orientation, Comma, Sp, orientationPrime, Colon, Sp, orientationType,
            Comma, RowBreak, Grp(),
            equalInputs, Sp, Rightarrow, RowBreak, Grp(),
            SettlementOf(admissible, scope, orientation, commitment),
            Sp, Eq, Sp,
            SettlementOf(admissible, scope, orientationPrime, commitmentPrime),
            Dot));
    }
}
