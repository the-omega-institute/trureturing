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
        if (!TryParseTarget(arguments, out var target, out var protectedBase))
        {
            return Usage();
        }

        try
        {
            var prepared = repository.Prepare(protectedBase);
            var baseline = Decode(repository.ReadRevision(prepared.Revision));
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

            var context = CurrentRuleContext.Create(current, policy, AcceptedLeanClosure.CreateWithoutReport());
            var evaluation = RuleCatalog.Default.EvaluateCurrentSingle(HeaderRuleId, context);
            var diagnostics = evaluation.Diagnostics.Where(diagnostic => diagnostic.Path == target).ToArray();
            if (diagnostics.Length > 0)
            {
                return new ExplicitCommandResult(
                    1,
                    string.Concat(diagnostics.Select(diagnostic => diagnostic.Render() + "\n")),
                    string.Empty);
            }

            var statePath = FrozenStatePath.FromModulePath(targetFile.Path);
            if (!baseline.Files.ContainsKey(statePath))
            {
                _ = RepositoryRules.TryHeader(targetFile.Text, out var header);
                var validation = UtilityDeclarationValidator.Validate(
                    UtilityValidationPhase.PreDeposit,
                    targetFile.Path,
                    header.Utility,
                    current,
                    () => leanReportSource.Load(current));
                if (!validation.IsAccepted)
                {
                    return UtilityFailure(target, validation);
                }

                if (baseline.Files.TryGetValue(targetFile.Path, out var previous)
                    && UtilityDeclarationValidator.IsClassificationDowngrade(previous, targetFile))
                {
                    return UtilityFailure(target, new UtilityValidationResult(validation.Declaration,
                        UtilityValidationFailure.ClassificationDowngrade, "reason=ordinary-body-unchanged"));
                }
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

    private static bool TryParseTarget(IReadOnlyList<string> arguments, out string target, out string? protectedBase)
    {
        target = string.Empty;
        protectedBase = null;
        if (arguments.Count != 4
            || !string.Equals(arguments[0], "--target", StringComparison.Ordinal)
            || !RepoPath.TryCreate(arguments[1], out var path)
            || arguments[2] != "--protected-base"
            || arguments[3].Length is not (40 or 64)
            || !arguments[3].All(char.IsAsciiHexDigit))
        {
            return false;
        }

        target = path.Value;
        protectedBase = arguments[3];
        return true;
    }

    private static ExplicitCommandResult Usage() => new(
        2,
        string.Empty,
        "USAGE: StrataLint deposit-header-check --target D5/.../*.lean --protected-base COMMIT_SHA\n");

    private static ExplicitCommandResult UtilityFailure(
        string module,
        UtilityValidationResult validation) =>
        new(
            1,
            $"{DepositFailureCode(validation.Failure)} module={module}"
                + (validation.Detail.Length == 0 ? "\n" : $" {validation.Detail}\n"),
            string.Empty);

    private static string DepositFailureCode(UtilityValidationFailure failure) => failure switch
    {
        UtilityValidationFailure.Missing => "DEPOSIT_HEADER_UTILITY_MISSING",
        UtilityValidationFailure.Syntax => "DEPOSIT_HEADER_UTILITY_SYNTAX",
        UtilityValidationFailure.InstanceMissing => "DEPOSIT_HEADER_UTILITY_INSTANCE_MISSING",
        UtilityValidationFailure.PremisesMissing => "DEPOSIT_HEADER_UTILITY_PREMISES_MISSING",
        UtilityValidationFailure.InputUnknown => "DEPOSIT_HEADER_UTILITY_INPUT_UNKNOWN",
        UtilityValidationFailure.TargetDangling => "DEPOSIT_HEADER_UTILITY_TARGET_DANGLING",
        UtilityValidationFailure.RefutesAtomNoCoverage =>
            "DEPOSIT_HEADER_UTILITY_REFUTES_ATOM_NO_COVERAGE",
        UtilityValidationFailure.ConsumerUnreachable =>
            "DEPOSIT_HEADER_UTILITY_CONSUMER_UNREACHABLE",
        UtilityValidationFailure.OrdinaryInstanceForbidden => "DEPOSIT_HEADER_UTILITY_ORDINARY_INSTANCE_BANNED",
        UtilityValidationFailure.ClassificationDowngrade => "DEPOSIT_HEADER_UTILITY_CLASSIFICATION_DOWNGRADE",
        UtilityValidationFailure.RefutationInvalid => "DEPOSIT_HEADER_UTILITY_REFUTATION_INVALID",
        UtilityValidationFailure.RefutationEvidenceMissing => "DEPOSIT_HEADER_UTILITY_REFUTATION_EVIDENCE_MISSING",
        _ => throw new ArgumentOutOfRangeException(nameof(failure)),
    };
}
