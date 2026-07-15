using System.Collections.Immutable;

namespace StrataLint.Cli;

internal sealed record ConservativeContractPlan(
    string PlanId,
    string Kind,
    ImmutableArray<string> ExactPaths,
    string RuleObligation,
    string CustodianKind,
    string CustodianReference,
    bool EvidencePresent,
    bool CustodianPresent);

internal sealed record ConservativeContractEpochCase(
    ImmutableArray<string> CandidateExactExclusions,
    ImmutableArray<string> CandidateRetiredRules,
    ImmutableArray<string> CandidateRemovedMatchers,
    ImmutableArray<ConservativeContractPlan> BaselinePlans,
    ImmutableArray<ConservativeContractPlan> CandidatePlans,
    ImmutableArray<string> BaselineConsumptions,
    ImmutableArray<string> CandidateConsumptions);

internal static class ContractEpochCorpusEvaluator
{
    private static readonly string TreeOid = "git-sha1:" + new string('f', 40);

    internal static ConservativeContractEpochCase? Materialize(GoldenContractEpochCase? source) =>
        source is null
            ? null
            : new ConservativeContractEpochCase(
                source.CandidateExactExclusions.ToImmutableArray(),
                source.CandidateRetiredRules.ToImmutableArray(),
                source.CandidateRemovedMatchers.ToImmutableArray(),
                source.BaselinePlans.Select(Materialize).ToImmutableArray(),
                source.CandidatePlans.Select(Materialize).ToImmutableArray(),
                source.BaselineConsumptions.ToImmutableArray(),
                source.CandidateConsumptions.ToImmutableArray());

    internal static object? Canonical(ConservativeContractEpochCase? source) => source is null
        ? null
        : new
        {
            baseline_consumptions = source.BaselineConsumptions,
            baseline_plans = source.BaselinePlans.Select(CanonicalPlan),
            candidate_consumptions = source.CandidateConsumptions,
            candidate_exact_exclusions = source.CandidateExactExclusions,
            candidate_plans = source.CandidatePlans.Select(CanonicalPlan),
            candidate_removed_matchers = source.CandidateRemovedMatchers,
            candidate_retired_rules = source.CandidateRetiredRules,
        };

    internal static void Validate(string caseId, ConservativeContractEpochCase? source)
    {
        if (source is null) return;
        if (source.BaselinePlans.IsDefault
            || source.CandidatePlans.IsDefault
            || source.BaselineConsumptions.IsDefault
            || source.CandidateConsumptions.IsDefault
            || source.CandidateExactExclusions.IsDefault
            || source.CandidateRetiredRules.IsDefault
            || source.CandidateRemovedMatchers.IsDefault)
        {
            throw new FormatException($"contract epoch corpus case is incomplete: {caseId}");
        }
    }

    internal static ConservativeContractCaseResult Evaluate(
        string goldenCaseId,
        ConservativeContractEpochCase source)
    {
        var caseId = "contract:" + goldenCaseId["golden:".Length..];
        try
        {
            var baselinePolicy = ConservativePolicySnapshot.Current();
            var candidatePolicy = baselinePolicy.WithExactExclusions(
                source.CandidateExactExclusions);
            foreach (var matcher in source.CandidateRemovedMatchers)
            {
                candidatePolicy = candidatePolicy.WithoutProtectionMatcher(matcher);
            }

            foreach (var rule in source.CandidateRetiredRules)
            {
                candidatePolicy = candidatePolicy.WithoutRuleObligation(rule);
            }

            BuiltPlans baselinePlans;
            BuiltPlans candidatePlans;
            try
            {
                baselinePlans = BuildPlans(source.BaselinePlans, baselinePolicy, candidatePolicy);
                candidatePlans = BuildPlans(source.CandidatePlans, baselinePolicy, candidatePolicy);
            }
            catch (ArgumentException)
            {
                return Result(caseId, "CONTRACT-EPOCH-PLAN-SCHEMA");
            }

            var baselineEvents = baselinePlans.Registrations.Cast<ContractEpochEvent>()
                .Concat(source.BaselineConsumptions.Select(static id =>
                    (ContractEpochEvent)new ContractEpochEvent.Consume(id)))
                .ToArray();
            var candidateEvents = baselineEvents
                .Concat(candidatePlans.Registrations)
                .Concat(source.CandidateConsumptions.Select(static id =>
                    (ContractEpochEvent)new ContractEpochEvent.Consume(id)))
                .ToArray();
            ContractEpochLedger baselineLedger;
            ContractEpochLedger candidateLedger;
            try
            {
                baselineLedger = RoundTrip(baselineEvents);
                candidateLedger = RoundTrip(candidateEvents);
            }
            catch (FormatException)
            {
                return Result(caseId, "CONTRACT-EPOCH-REPLAY");
            }

            var paths = baselinePlans.ExistingPaths.Concat(candidatePlans.ExistingPaths);
            var anchors = baselinePlans.C0Anchors.Concat(candidatePlans.C0Anchors);
            var comparison = ContractEpochVerifier.Verify(new ContractEpochComparisonInput(
                TreeOid,
                baselinePolicy,
                candidatePolicy,
                baselineLedger,
                candidateLedger,
                ContractEpochEvidenceIndex.Create(baselinePlans.Receipts, paths, anchors),
                ContractEpochEvidenceIndex.Create(
                    baselinePlans.Receipts.Concat(candidatePlans.Receipts),
                    paths,
                    anchors)));
            return new ConservativeContractCaseResult(
                caseId,
                comparison.Findings.Select(static item => item.Code)
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal)
                    .ToImmutableArray());
        }
        catch (InvalidOperationException)
        {
            return Result(caseId, "CONTRACT-EPOCH-REPLAY");
        }
    }

    private static BuiltPlans BuildPlans(
        IEnumerable<ConservativeContractPlan> plans,
        ConservativePolicySnapshot baseline,
        ConservativePolicySnapshot candidate)
    {
        var registrations = ImmutableArray.CreateBuilder<ContractEpochEvent.Register>();
        var receipts = ImmutableArray.CreateBuilder<ContractEpochEvidenceReceipt>();
        var existingPaths = ImmutableArray.CreateBuilder<string>();
        var c0Anchors = ImmutableArray.CreateBuilder<string>();
        foreach (var source in plans)
        {
            var built = BuildPlan(source, candidate);
            registrations.Add(new ContractEpochEvent.Register(
                source.PlanId,
                TreeOid,
                baseline.Root,
                candidate.Root,
                built.Plan));
            if (source.EvidencePresent) receipts.Add(built.Receipt);
            if (source.CustodianPresent && built.Custodian is { } custodian)
            {
                if (custodian.Kind is MachineCustodianKind.Loader)
                {
                    existingPaths.Add(custodian.Reference);
                }
                else if (custodian.Kind is MachineCustodianKind.C0Anchor)
                {
                    c0Anchors.Add(custodian.Reference);
                }
            }
        }

        return new BuiltPlans(
            registrations.ToImmutable(),
            receipts.ToImmutable(),
            existingPaths.ToImmutable(),
            c0Anchors.ToImmutable());
    }

    private static BuiltPlan BuildPlan(
        ConservativeContractPlan source,
        ConservativePolicySnapshot candidate)
    {
        switch (source.Kind)
        {
            case "custody_transfer":
                var custodian = new MachineCustodian(
                    ParseCustodianKind(source.CustodianKind),
                    source.CustodianReference);
                var custody = ContractEpochEvidenceReceipt.Custody(
                    candidate.Root,
                    source.ExactPaths,
                    custodian);
                return new BuiltPlan(
                    new TransitionPlan.CustodyTransferV1(
                        source.ExactPaths,
                        custodian,
                        custody.Reference),
                    custody,
                    custodian);
            case "discharge_paths":
                var pathProof = ContractEpochEvidenceReceipt.UnreachabilityForPaths(
                    candidate.Root,
                    source.ExactPaths);
                return new BuiltPlan(
                    new TransitionPlan.AuthorityDischargeV1(
                        source.ExactPaths,
                        null,
                        pathProof.Reference),
                    pathProof,
                    null);
            case "discharge_rule":
                var ruleProof = ContractEpochEvidenceReceipt.UnreachabilityForRule(
                    candidate.Root,
                    source.RuleObligation);
                return new BuiltPlan(
                    new TransitionPlan.AuthorityDischargeV1(
                        [],
                        source.RuleObligation,
                        ruleProof.Reference),
                    ruleProof,
                    null);
            default:
                throw new ArgumentException($"unknown contract corpus plan kind: {source.Kind}");
        }
    }

    private static ConservativeContractPlan Materialize(GoldenContractPlan source) => new(
        source.PlanId,
        source.Kind switch
        {
            GoldenContractPlanKind.CustodyTransfer => "custody_transfer",
            GoldenContractPlanKind.DischargePaths => "discharge_paths",
            GoldenContractPlanKind.DischargeRule => "discharge_rule",
            _ => throw new InvalidOperationException("unknown golden contract plan kind"),
        },
        source.ExactPaths.ToImmutableArray(),
        source.RuleObligation,
        source.CustodianKind,
        source.CustodianReference,
        source.EvidencePresent,
        source.CustodianPresent);

    private static object CanonicalPlan(ConservativeContractPlan source) => new
    {
        custodian_kind = source.CustodianKind,
        custodian_present = source.CustodianPresent,
        custodian_reference = source.CustodianReference,
        evidence_present = source.EvidencePresent,
        exact_paths = source.ExactPaths,
        kind = source.Kind,
        plan_id = source.PlanId,
        rule_obligation = source.RuleObligation,
    };

    private static ContractEpochLedger RoundTrip(IEnumerable<ContractEpochEvent> events) =>
        ContractEpochLedgerCodec.Read(ContractEpochLedgerCodec.Write(events).AsSpan());

    private static MachineCustodianKind ParseCustodianKind(string value) => value switch
    {
        "loader" => MachineCustodianKind.Loader,
        "c0_anchor" => MachineCustodianKind.C0Anchor,
        "rule_id" => MachineCustodianKind.RuleId,
        _ => throw new ArgumentException($"unknown contract corpus custodian kind: {value}"),
    };

    private static ConservativeContractCaseResult Result(string caseId, string code) =>
        new(caseId, [code]);

    private static void RequireSortedUnique(IEnumerable<string> values, string context)
    {
        string? previous = null;
        foreach (var value in values)
        {
            if (string.IsNullOrWhiteSpace(value)
                || previous is not null && string.CompareOrdinal(previous, value) >= 0)
            {
                throw new FormatException($"contract corpus {context} must be sorted and unique");
            }

            previous = value;
        }
    }

    private sealed record BuiltPlan(
        TransitionPlan Plan,
        ContractEpochEvidenceReceipt Receipt,
        MachineCustodian? Custodian);

    private sealed record BuiltPlans(
        ImmutableArray<ContractEpochEvent.Register> Registrations,
        ImmutableArray<ContractEpochEvidenceReceipt> Receipts,
        ImmutableArray<string> ExistingPaths,
        ImmutableArray<string> C0Anchors);
}
