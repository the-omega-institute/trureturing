using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DepositHeaderCheckCommand
{
    private static readonly RuleId HeaderRuleId = RuleId.CreateKnown(12);

    internal static ExplicitCommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);
        if (!TryParseTarget(arguments, out var target))
        {
            return Usage();
        }

        try
        {
            var current = Decode(repository.ReadCurrent());
            if (!current.TryGetFile(target, out var targetFile))
            {
                throw new InvalidOperationException($"deposit target does not exist: {target}");
            }

            var policy = LoadPolicy(current);
            var applicable = RuleCatalog.Default.ApplicableTo(
                targetFile,
                RuleApplicabilityContext.Create(current, policy));
            if (!applicable.Any(descriptor => descriptor.Id == HeaderRuleId))
            {
                throw new InvalidOperationException(
                    $"deposit target is outside the registered SL-012 scope: {target}");
            }

            var lean = LeanClosureValidator.Validate(current, leanReportSource.Load(current)) switch
            {
                LeanValidationOutcome.Accepted accepted => accepted.Capability,
                LeanValidationOutcome.InfrastructureFailure failure =>
                    throw new InvalidOperationException(failure.Message),
            };
            var changes = RawChangeSet.Create([target]);
            var metaClear = BootstrapGate.Evaluate(changes) switch
            {
                BootstrapOutcome.Clear clear => clear.Capability,
                BootstrapOutcome.InfrastructureFailure failure =>
                    throw new InvalidOperationException(failure.Message),
                BootstrapOutcome.ProtectedSurfaceVerificationRequired =>
                    throw new InvalidOperationException("deposit target unexpectedly enters protected surface"),
            };
            var context = RuleEvaluationContext.Create(
                current,
                current,
                policy,
                lean,
                changes,
                metaClear);
            var evaluation = RuleCatalog.Default.EvaluateSingle(HeaderRuleId, context);
            if (!evaluation.Diagnostics.IsEmpty)
            {
                return new ExplicitCommandResult(
                    1,
                    string.Concat(evaluation.Diagnostics.Select(diagnostic => diagnostic.Render() + "\n")),
                    string.Empty);
            }

            return new ExplicitCommandResult(
                0,
                $"DEPOSIT_HEADER_CHECKED {HeaderRuleId.Value} {target}\n",
                string.Empty);
        }
        catch (Exception exception) when (
            exception is InvalidOperationException
                or FormatException
                or ArgumentException
                or IOException)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"DEPOSIT_HEADER_CHECK_INVALID {exception.Message}\n");
        }
    }

    private static ValidatedPolicy LoadPolicy(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile("Meta/registry.yaml", out var registry)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domains))
        {
            throw new InvalidOperationException(
                "current snapshot lacks Meta/registry.yaml or Meta/domains.yaml");
        }

        return RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
        {
            RegistryLoadOutcome.Accepted accepted => accepted.Policy,
            RegistryLoadOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static bool TryParseTarget(IReadOnlyList<string> arguments, out string target)
    {
        target = string.Empty;
        if (arguments.Count != 2
            || !string.Equals(arguments[0], "--target", StringComparison.Ordinal)
            || !RepoPath.TryCreate(arguments[1], out var path))
        {
            return false;
        }

        target = path.Value;
        return true;
    }

    private static ExplicitCommandResult Usage() => new(
        2,
        string.Empty,
        "USAGE: StrataLint deposit-header-check --target D5/.../*.lean\n");
}
