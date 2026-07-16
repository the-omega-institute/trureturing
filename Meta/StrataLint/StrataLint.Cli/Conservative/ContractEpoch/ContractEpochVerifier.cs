using System.Collections.Immutable;

namespace StrataLint.Cli;

internal sealed record ContractPolicyDelta(
    ImmutableArray<string> RetiredExactPaths,
    ImmutableArray<string> RetiredRuleObligations,
    ImmutableArray<string> OpaqueRetirements);

internal sealed record ContractEpochComparisonInput(
    string BaselineTreeOid,
    ConservativePolicySnapshot BaselinePolicy,
    ConservativePolicySnapshot CandidatePolicy,
    ContractEpochLedger BaselineLedger,
    ContractEpochLedger CandidateLedger,
    ContractEpochEvidenceIndex BaselineEvidence,
    ContractEpochEvidenceIndex CandidateEvidence);

internal sealed record ContractEpochFinding(string Code, string Subject, string Message);

internal sealed record ContractEpochComparisonResult(
    bool Accepted,
    ContractPolicyDelta PolicyDelta,
    ImmutableArray<string> UncoveredObligations,
    ImmutableArray<ContractEpochFinding> Findings);

internal static class ContractEpochVerifier
{
    private const string C0CertificatePath =
        "Meta/StrataLint/Golden/c0-inaugural-conservative-certificate.json";
    private const string CanonicalWriterPath =
        "Meta/StrataLint/StrataLint.Engine/Snapshot/StructuredCanonicalWriter.cs";
    private const string TowerManifestPath = "Meta/StrataLint/TOWER.yaml";

    private static readonly ImmutableArray<string> UnshrinkablePrefixes =
    [
        ".github/",
        "Meta/StrataLint/Golden/Frozen/",
        "Meta/StrataLint/StrataLint.Cli/Conservative/",
        "Meta/StrataLint/StrataLint.Engine/Admission/",
        "Meta/contract-epoch/",
    ];

    private static readonly ImmutableHashSet<string> UnshrinkableExactPaths =
        new[]
        {
            C0CertificatePath,
            CanonicalWriterPath,
            TowerManifestPath,
        }.ToImmutableHashSet(StringComparer.Ordinal);

    private static readonly ImmutableHashSet<string> UnshrinkableRules =
        new[] { "SL-022" }.ToImmutableHashSet(StringComparer.Ordinal);

    internal static ContractEpochComparisonResult Verify(ContractEpochComparisonInput input)
    {
        ArgumentNullException.ThrowIfNull(input);
        var treeOid = ContractEpochSyntax.TreeOid(input.BaselineTreeOid);
        var delta = ComputePolicyDelta(input.BaselinePolicy, input.CandidatePolicy);
        var ledger = ContractEpochLedger.Compare(input.BaselineLedger, input.CandidateLedger);
        var findings = ImmutableArray.CreateBuilder<ContractEpochFinding>();
        var uncovered = delta.RetiredExactPaths.Select(static path => "path:" + path)
            .Concat(delta.RetiredRuleObligations.Select(static rule => "rule:" + rule))
            .Concat(delta.OpaqueRetirements.Select(static atom => "policy:" + atom))
            .ToHashSet(StringComparer.Ordinal);

        foreach (var atom in delta.OpaqueRetirements)
        {
            findings.Add(new ContractEpochFinding(
                "CONTRACT-EPOCH-OPAQUE-RETIREMENT",
                atom,
                "matcher-level policy contraction cannot be authorized by an exact transition plan"));
        }

        foreach (var path in delta.RetiredExactPaths.Where(IsUnshrinkable))
        {
            findings.Add(Unshrinkable("path:" + path));
        }

        foreach (var rule in delta.RetiredRuleObligations.Where(UnshrinkableRules.Contains))
        {
            findings.Add(Unshrinkable("rule:" + rule));
        }

        foreach (var registration in ledger.NewRegistrations)
        {
            ValidateRegistrationBinding(
                registration,
                requireTreeOid: treeOid,
                input.BaselinePolicy.Root,
                requirePostRoot: null,
                findings);
            ValidatePlanEvidence(
                registration,
                input.CandidatePolicy,
                input.CandidateEvidence,
                findings);
        }

        foreach (var planId in ledger.IneligibleConsumptions)
        {
            findings.Add(new ContractEpochFinding(
                "CONTRACT-EPOCH-CANDIDATE-PLAN-INELIGIBLE",
                planId,
                "only a plan registered and pending in the exact base commit may be consumed"));
        }

        foreach (var registration in ledger.EligibleConsumptions)
        {
            var before = findings.Count;
            ValidateRegistrationBinding(
                registration,
                requireTreeOid: null,
                input.BaselinePolicy.Root,
                input.CandidatePolicy.Root,
                findings);
            var claims = Claims(registration.Plan);
            if (claims.Any(claim => !uncovered.Contains(claim)))
            {
                findings.Add(new ContractEpochFinding(
                    "CONTRACT-EPOCH-SCOPE-OUTSIDE-DELTA",
                    registration.PlanId,
                    "transition plan scope is not an exact subset of the computed retirement delta"));
            }

            if (claims.Any(IsUnshrinkableClaim))
            {
                findings.Add(Unshrinkable(registration.PlanId));
            }

            ValidatePlanEvidence(
                registration,
                input.CandidatePolicy,
                input.BaselineEvidence,
                findings);
            if (findings.Count == before)
            {
                foreach (var claim in claims) uncovered.Remove(claim);
            }
        }

        foreach (var obligation in uncovered.Order(StringComparer.Ordinal))
        {
            findings.Add(new ContractEpochFinding(
                "CONTRACT-EPOCH-UNCOVERED-OBLIGATION",
                obligation,
                "retired policy atom has no valid custody transfer or authority discharge"));
        }

        var orderedFindings = findings
            .OrderBy(static item => item.Code, StringComparer.Ordinal)
            .ThenBy(static item => item.Subject, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal)
            .ToImmutableArray();
        var orderedUncovered = uncovered.Order(StringComparer.Ordinal).ToImmutableArray();
        return new ContractEpochComparisonResult(
            orderedFindings.IsEmpty && orderedUncovered.IsEmpty,
            delta,
            orderedUncovered,
            orderedFindings);
    }

    internal static ContractPolicyDelta ComputePolicyDelta(
        ConservativePolicySnapshot baseline,
        ConservativePolicySnapshot candidate)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(candidate);
        var opaque = ImmutableArray.CreateBuilder<string>();
        var candidateMatchers = candidate.ProtectionMatchers.ToDictionary(
            static item => item.Id,
            StringComparer.Ordinal);
        foreach (var matcher in baseline.ProtectionMatchers)
        {
            if (!candidateMatchers.TryGetValue(matcher.Id, out var current) || current != matcher)
            {
                opaque.Add("protection:" + matcher.Id);
            }
        }

        foreach (var prefix in candidate.LegacyPrefixExclusions.Where(prefix =>
            !baseline.LegacyPrefixExclusions.Contains(prefix, StringComparer.Ordinal)))
        {
            opaque.Add("legacy-exclusion:" + prefix);
        }

        var retiredPaths = candidate.ExactExclusions
            .Where(path => !baseline.ExactExclusions.Contains(path, StringComparer.Ordinal))
            .Where(path => baseline.IsProtected(path) && !candidate.IsProtected(path))
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var candidateRules = candidate.RuleObligations.ToDictionary(
            static item => item.RuleId,
            StringComparer.Ordinal);
        var retiredRules = baseline.RuleObligations
            .Where(item => !candidateRules.TryGetValue(item.RuleId, out var current)
                || current != item)
            .Select(static item => item.RuleId)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        return new ContractPolicyDelta(
            retiredPaths,
            retiredRules,
            opaque.Order(StringComparer.Ordinal).ToImmutableArray());
    }

    private static void ValidateRegistrationBinding(
        ContractEpochEvent.Register registration,
        string? requireTreeOid,
        string prePolicyRoot,
        string? requirePostRoot,
        ImmutableArray<ContractEpochFinding>.Builder findings)
    {
        if (requireTreeOid is not null
                && !string.Equals(
                    registration.BaselineTreeOid,
                    requireTreeOid,
                    StringComparison.Ordinal)
            || !string.Equals(registration.PrePolicyRoot, prePolicyRoot, StringComparison.Ordinal)
            || requirePostRoot is not null && !string.Equals(
                registration.PostPolicyRoot,
                requirePostRoot,
                StringComparison.Ordinal))
        {
            findings.Add(new ContractEpochFinding(
                "CONTRACT-EPOCH-ROOT-DRIFT",
                registration.PlanId,
                "transition plan is not bound to the exact base tree and pre/post policy roots"));
        }
    }

    private static void ValidatePlanEvidence(
        ContractEpochEvent.Register registration,
        ConservativePolicySnapshot candidate,
        ContractEpochEvidenceIndex evidence,
        ImmutableArray<ContractEpochFinding>.Builder findings)
    {
        var reference = registration.Plan switch
        {
            TransitionPlan.CustodyTransferV1 transfer => transfer.Receipt,
            TransitionPlan.AuthorityDischargeV1 discharge => discharge.UnreachabilityProofRef,
            _ => throw new InvalidOperationException("unknown transition plan"),
        };
        if (!evidence.Receipts.TryGetValue(reference, out var receipt)
            || !string.Equals(
                receipt.PolicyRoot,
                registration.PostPolicyRoot,
                StringComparison.Ordinal))
        {
            findings.Add(new ContractEpochFinding(
                "CONTRACT-EPOCH-EVIDENCE-INVALID",
                registration.PlanId,
                "transition evidence is missing or bound to a different target policy root"));
            return;
        }

        switch (registration.Plan)
        {
            case TransitionPlan.CustodyTransferV1 transfer:
                if (receipt.Kind is not ContractEpochEvidenceKind.Custody
                    || !receipt.ExactPaths.SequenceEqual(transfer.ExactPaths, StringComparer.Ordinal)
                    || receipt.Custodian is null
                    || receipt.Custodian.Kind != transfer.NewCustodian.Kind
                    || !string.Equals(
                        receipt.Custodian.Reference,
                        transfer.NewCustodian.Reference,
                        StringComparison.Ordinal))
                {
                    findings.Add(new ContractEpochFinding(
                        "CONTRACT-EPOCH-EVIDENCE-INVALID",
                        registration.PlanId,
                        "custody receipt does not exactly attest the plan scope and custodian"));
                }
                else if (!evidence.CustodianExists(transfer.NewCustodian, candidate))
                {
                    findings.Add(new ContractEpochFinding(
                        "CONTRACT-EPOCH-CUSTODIAN-INVALID",
                        registration.PlanId,
                        "new custodian is not machine-verifiable in the candidate policy/tree"));
                }

                break;
            case TransitionPlan.AuthorityDischargeV1 discharge:
                if (receipt.Kind is not ContractEpochEvidenceKind.Unreachability
                    || !receipt.ExactPaths.SequenceEqual(discharge.ExactPaths, StringComparer.Ordinal)
                    || !string.Equals(
                        receipt.RuleObligation,
                        discharge.RuleObligation,
                        StringComparison.Ordinal))
                {
                    findings.Add(new ContractEpochFinding(
                        "CONTRACT-EPOCH-EVIDENCE-INVALID",
                        registration.PlanId,
                        "unreachability proof does not exactly attest the discharge scope"));
                }

                break;
        }
    }

    private static ImmutableArray<string> Claims(TransitionPlan plan) => plan switch
    {
        TransitionPlan.CustodyTransferV1 transfer => transfer.ExactPaths
            .Select(static path => "path:" + path).ToImmutableArray(),
        TransitionPlan.AuthorityDischargeV1 discharge when discharge.RuleObligation is null =>
            discharge.ExactPaths.Select(static path => "path:" + path).ToImmutableArray(),
        TransitionPlan.AuthorityDischargeV1 discharge => ["rule:" + discharge.RuleObligation],
        _ => throw new InvalidOperationException("unknown transition plan"),
    };

    private static bool IsUnshrinkable(string path) =>
        UnshrinkableExactPaths.Contains(path)
        || UnshrinkablePrefixes.Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal));

    private static bool IsUnshrinkableClaim(string claim) =>
        claim.StartsWith("path:", StringComparison.Ordinal)
            ? IsUnshrinkable(claim["path:".Length..])
            : claim.StartsWith("rule:", StringComparison.Ordinal)
                && UnshrinkableRules.Contains(claim["rule:".Length..]);

    private static ContractEpochFinding Unshrinkable(string subject) => new(
        "CONTRACT-EPOCH-UNSHRINKABLE",
        subject,
        "contract epoch has no authority over its verifier, gate, workflow, writer, or frozen roots");
}
