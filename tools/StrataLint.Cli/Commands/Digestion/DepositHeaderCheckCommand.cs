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
                AcceptedLeanClosure.CreateWithoutReport(),
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

            var statePath = FrozenStatePath.FromModulePath(targetFile.Path);
            if (!current.Files.ContainsKey(statePath))
            {
                _ = RepositoryRules.TryHeader(targetFile.Text, out var header);
                if (!UtilitySyntax.TryParse(header.Utility, out var utility, out var failure))
                {
                    var code = failure switch
                    {
                        UtilityParseFailure.Missing => "DEPOSIT_HEADER_UTILITY_MISSING",
                        UtilityParseFailure.InstanceMissing => "DEPOSIT_HEADER_UTILITY_INSTANCE_MISSING",
                        UtilityParseFailure.PremisesMissing => "DEPOSIT_HEADER_UTILITY_PREMISES_MISSING",
                        _ => "DEPOSIT_HEADER_UTILITY_SYNTAX",
                    };
                    return new ExplicitCommandResult(
                        1,
                        $"{code} module={target}\n",
                        string.Empty);
                }

                if (utility!.Kind is not UtilityKind.None)
                {
                    var report = leanReportSource.Load(current);
                    foreach (var gid in UtilityAdmissionRule.DeclarationReferences(utility))
                    {
                        var targetPath = ((Target.Formal)gid.ToTarget()).Path;
                        if (!report.Files.TryGetValue(targetPath, out var targetReport)
                            || targetReport.Error is not null)
                        {
                            return UtilityFailure(
                                "DEPOSIT_HEADER_UTILITY_INPUT_UNKNOWN",
                                target,
                                $"target_module={targetPath.Value} reason=current-lean-report-missing");
                        }

                        if (!UtilityAdmissionRule.TryResolveDeclaration(gid, targetReport, out _))
                        {
                            return UtilityFailure(
                                "DEPOSIT_HEADER_UTILITY_TARGET_DANGLING",
                                target,
                                $"target={gid.Value}");
                        }
                    }

                    var softTarget = utility.BasisTarget;
                    if (softTarget is { Kind: UtilityTargetKind.Atom or UtilityTargetKind.Task })
                    {
                        BackfillInventoryDocument inventory;
                        try
                        {
                            inventory = BackfillInventoryLoader.Load(current);
                        }
                        catch (FormatException)
                        {
                            return UtilityFailure(
                                "DEPOSIT_HEADER_UTILITY_INPUT_UNKNOWN",
                                target,
                                "reason=backfill-load-failed");
                        }

                        var exists = softTarget.Kind switch
                        {
                            UtilityTargetKind.Atom => inventory.RequireDigestionEntries().Any(entry =>
                                string.Equals(entry.AtomId, softTarget.Value, StringComparison.Ordinal)),
                            UtilityTargetKind.Task => inventory.RequireTickets().Any(ticket =>
                                string.Equals(ticket.CaseId, softTarget.Value, StringComparison.Ordinal)),
                            _ => true,
                        };
                        if (!exists)
                        {
                            var prefix = softTarget.Kind is UtilityTargetKind.Atom ? "atom:" : "task:";
                            return UtilityFailure(
                                "DEPOSIT_HEADER_UTILITY_TARGET_DANGLING",
                                target,
                                $"target={prefix}{softTarget.Value}");
                        }
                    }
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

    private static ExplicitCommandResult UtilityFailure(
        string code,
        string module,
        string detail) =>
        new(
            1,
            $"{code} module={module} {detail}\n",
            string.Empty);
}
