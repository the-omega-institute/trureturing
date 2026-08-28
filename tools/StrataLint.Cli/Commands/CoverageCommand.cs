using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class CoverageCommand
{
    internal static CommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        try
        {
            var json = ParseArguments(arguments);
            var snapshot = Decode(repository.ReadCurrent());
            var policy = LoadPolicy(snapshot);
            var lean = ValidateLean(snapshot, leanReportSource.Load(snapshot));
            var states = LeanTruthStates.Resolve(snapshot, lean);
            var frozen = LoadFrozenPaths(snapshot);
            var ledger = CoverageLedgerIndex.FromStates(
                states,
                frozen,
                snapshot);
            var tower = LoadTower(snapshot);
            var validatedTower = TowerManifestValidator.Validate(tower, snapshot, RuleCatalog.Default);
            if (validatedTower is TowerValidationOutcome.Rejected invalidTower)
            {
                throw new InvalidOperationException(
                    "tower validation failed: "
                    + string.Join(
                        "; ",
                        invalidTower.Findings.Select(static item =>
                            $"{item.Code}/{item.Component}: {item.Message}")));
            }

            var report = CoverageAnalyzer.Analyze(snapshot, policy, RuleCatalog.Default, ledger);
            var bytes = json
                ? CoverageCanonicalWriter.WriteJson(
                    report,
                    ((TowerValidationOutcome.Accepted)validatedTower).Manifest)
                : CoverageCanonicalWriter.WriteText(
                    report,
                    ((TowerValidationOutcome.Accepted)validatedTower).Manifest);
            return new CommandResult(true, Encoding.UTF8.GetString(bytes.AsSpan()), string.Empty);
        }
        catch (Exception exception) when (
            exception is InvalidOperationException or FormatException or DecoderFallbackException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"INFRASTRUCTURE_FAILURE coverage: {exception.Message}\n");
        }
    }

    private static bool ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 0) return false;
        if (arguments.Count == 1 && arguments[0] == "--json") return true;
        throw new InvalidOperationException("USAGE: StrataLint coverage [--json]");
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static ValidatedPolicy LoadPolicy(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile("Meta/registry.yaml", out var registry)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domains))
        {
            throw new InvalidOperationException("coverage requires Meta/registry.yaml and Meta/domains.yaml");
        }

        return RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
        {
            RegistryLoadOutcome.Accepted accepted => accepted.Policy,
            RegistryLoadOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
    }

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static ImmutableArray<RepoPath> LoadFrozenPaths(RepositorySnapshot snapshot)
    {
        var files = snapshot.Files.Values
            .Where(file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value))
            .ToArray();
        if (files.Length == 0)
        {
            throw new InvalidOperationException("frozen ledger is missing");
        }

        var events = DagLedgerCommandPreparation.LoadTrustedLedgerFiles(files, "frozen ledger");
        return FrozenCoverageLedger.Load(events) switch
        {
            FrozenCoverageLoadOutcome.Loaded loaded => loaded.ActiveFrozenPaths,
            FrozenCoverageLoadOutcome.Invalid invalid =>
                throw new InvalidOperationException(invalid.Message),
        };
    }

    private static TowerManifestSyntax LoadTower(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(RepositoryRules.TowerManifestPath, out var file))
        {
            throw new InvalidOperationException(
                $"tower manifest is missing: {RepositoryRules.TowerManifestPath}");
        }

        return TowerManifestParser.Parse(file.RawBytes.AsSpan()) switch
        {
            TowerManifestParseOutcome.Loaded loaded => loaded.Syntax,
            TowerManifestParseOutcome.Invalid invalid =>
                throw new InvalidOperationException(invalid.Message),
        };
    }
}
