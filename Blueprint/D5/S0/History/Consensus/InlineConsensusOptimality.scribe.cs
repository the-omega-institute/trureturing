using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Carrier selection identifies every available priority minimum, configurations certify their initial dispatch plans, and legal untried roles have an eligible assignment or abstain.",
        H("Inline Consensus Optimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("carrier-selection-is-available-and-identifies-every-priority-minimum"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusOptimality."
                    + "selectCarrier_is_unique_minimum"),
                H("Carrier selection is available and identifies every priority minimum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("eligible"), Comma, Sp, F.Id("tried"), Comma, Esc,
                    Call("Nonempty", EligibleUntried()), Sp, Rightarrow, Sp,
                    Call("selectCarrier", F.Id("eligible"), F.Id("tried")), Sp,
                    InMacro, Sp, EligibleUntried(),
                    RowBreak, Sp, Land, Sp,
                    Forall, Sp, F.Id("other"), Comma, Esc,
                    F.Id("other"), Sp, InMacro, Sp, EligibleUntried(), Sp,
                    Rightarrow, Sp,
                    Open, Forall, Sp, F.Id("carrier"), Comma, Esc,
                    F.Id("carrier"), Sp, InMacro, Sp, EligibleUntried(), Sp,
                    Rightarrow, Sp,
                    Call("priorityRank", F.Id("other")), Sp, Le, Sp,
                    Call("priorityRank", F.Id("carrier")), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("other"), Sp, Eq, Sp,
                    Call("selectCarrier", F.Id("eligible"), F.Id("tried"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Whenever the eligible carriers not yet tried form a nonempty finite set, "
                        + "selectCarrier belongs to that set. Any other available carrier whose "
                        + "priority rank is no greater than every available carrier's rank must equal "
                        + "the selected carrier.")),
                    Paragraph(Text(
                        "The result is conditional on a nonempty eligible-untried set. It does not say "
                        + "that a worker carrier is always available, and the separate exhaustion row "
                        + "selects abstain when that set is empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-perspective-consensus-is-rejected"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusOptimality."
                    + "design_router_rejects_single_perspective"),
                H("Single-perspective consensus is rejected"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("designRouter", F.Id("singlePerspective")), Sp, Eq, Sp,
                    F.Id("rejectFakeConsensus")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The singlePerspective row of designRouter returns rejectFakeConsensus. "
                        + "This equation states one router row; it does not "
                        + "supply an independent design hazard predicate or a design-router maximality "
                        + "theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("protocol-configurations-certify-their-initial-plans"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusOptimality.ProtocolConfig"),
                H("Protocol configurations certify their initial plans"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "ProtocolConfig stores eligibility and retry-budget functions, a DispatchPlan, "
                        + "a GoalArtifact, the shared-pass budget and its owner-authorization flag, "
                        + "and the initial isolation status. Its initialPlanCompatible field is a "
                        + "proof of InitialPlanCompatible eligible dispatchPlan, so plan compatibility "
                        + "is part of every configuration value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a-legal-untried-role-has-an-eligible-planned-carrier-or-selects-abstain"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusOptimality."
                    + "legal_worker_stage_initially_progresses_or_abstains"),
                H("A legal untried role has an eligible planned carrier or selects abstain"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("config"), Comma, Sp, F.Id("state"), Comma, Sp,
                    F.Id("role"), Comma, Esc,
                    Call("LegalAt", F.Id("role"), Field("state", "stage")),
                    Sp, Rightarrow, Sp,
                    Call("triedAt", F.Id("state"), Field("state", "stage"), F.Id("role")),
                    Sp, Eq, Sp, Varnothing, Sp, Rightarrow, Sp, Open,
                    Open, Exists, Sp, F.Id("carrier"), Comma, Esc,
                    Call("InitiallyAssigned", F.Id("config"), F.Id("state"), F.Id("role"),
                        F.Id("carrier")),
                    Sp, Land, Sp,
                    Call("CarrierLegalAt", Field("state", "stage"), F.Id("role"),
                        F.Id("carrier")),
                    Sp, Land, Sp,
                    ConfigEligible(Field("state", "stage"), F.Id("role"), F.Id("carrier")),
                    Sp, Eq, Sp, F.Id("true"), Close,
                    Sp, Lor, Sp,
                    Call("selectCarrier",
                        ConfigEligible(Field("state", "stage"), F.Id("role")),
                        Call("triedAt", F.Id("state"), Field("state", "stage"), F.Id("role"))),
                    Sp, Eq, Sp, F.Id("abstain"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a role legal at the state's stage, if no carrier has yet been tried for "
                        + "that role, the conclusion is a disjunction: either some carrier is the "
                        + "initially assigned, stage-legal, eligible carrier, or selectCarrier on the "
                        + "same eligibility and tried set returns abstain.")),
                    Paragraph(Text(
                        "The proof uses DispatchPlan.carrierAt for the legal role and the configuration's "
                        + "initialPlanCompatible proof to establish the existential left disjunct. "
                        + "It does not claim progress for a role that is illegal at the current stage."))),
                DescribeRole.Theorem))));

    private static Formula EligibleUntried() =>
        Call("eligibleUntried", F.Id("eligible"), F.Id("tried"));

    private static Formula Field(string subject, string field) =>
        Seq(F.Id(subject), Dot, F.Id(field));

    private static Formula ConfigEligible(Formula stage, Formula role) =>
        Seq(Field("config", "eligible"), Open, stage, Comma, Sp, role, Close);

    private static Formula ConfigEligible(Formula stage, Formula role, Formula carrier) =>
        Seq(Field("config", "eligible"), Open, stage, Comma, Sp, role, Comma, Sp,
            carrier, Close);
}
