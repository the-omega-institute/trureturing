using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerGenesisWriter
{
    private const string GeneratorSourcePath =
        "Meta/StrataLint/StrataLint.Cli/DagLedgerGenesisWriter.cs";

    internal static CommandResult Generate(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanInspector leanInspector,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--revision")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-genesis --revision EXACT_COMMIT_OID");
            }

            var identity = repository.ResolveFrozenRevision(arguments[1]);
            var snapshot = Decode(repository.ReadFrozenRevision(identity.Revision));
            var lean = ValidateLean(snapshot, leanInspector.Inspect(snapshot));
            var dag = AcyclicTruthDag.Build(snapshot, lean) switch
            {
                DagBuildOutcome.Accepted accepted => accepted.Capability,
                DagBuildOutcome.Rejected rejected => throw new InvalidOperationException(
                    "origin revision truth DAG is cyclic: "
                    + string.Join(" -> ", rejected.Witness.Select(static path => path.Value))),
                _ => throw new InvalidOperationException("unknown truth DAG outcome"),
            };
            if (!snapshot.TryGetFile("lean-toolchain", out var toolchain)
                || !snapshot.TryGetFile("lake-manifest.json", out var manifest))
            {
                throw new InvalidOperationException("origin revision lacks pinned Lean environment files");
            }

            var algorithm = identity.CommitOid.StartsWith("git-sha256:", StringComparison.Ordinal)
                ? HashAlgorithmName.SHA256
                : HashAlgorithmName.SHA1;
            var environment = new FrozenEnvironmentAttestation(
                identity.CommitOid,
                identity.TreeOid,
                GitBlobOid(toolchain.RawBytes.AsSpan(), algorithm),
                GitBlobOid(manifest.RawBytes.AsSpan(), algorithm));
            var attestations = dag.Nodes
                .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
                .Select(node => new FrozenModuleAttestation(
                    node.RepoPath,
                    GitBlobOid(snapshot.Files[node.RepoPath].RawBytes.AsSpan(), algorithm)))
                .ToImmutableArray();
            var catalog = FrozenContentAddress.Build(snapshot, lean, dag, environment, attestations) switch
            {
                FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
                FrozenMaterialOutcome.Rejected rejected => throw new InvalidOperationException(rejected.Message),
                _ => throw new InvalidOperationException("unknown frozen material outcome"),
            };
            var generatorPath = Path.Combine(
                repositoryRoot,
                GeneratorSourcePath.Replace('/', Path.DirectorySeparatorChar));
            var descriptor = new FrozenGenesisDescriptor(
                GitBlobOid(File.ReadAllBytes(generatorPath), algorithm),
                RuleCatalog.Default.RootSha256);
            var first = FrozenLedgerGenerator.GenerateGenesis(catalog, descriptor);
            var second = FrozenLedgerGenerator.GenerateGenesis(catalog, descriptor);
            if (!first.AsSpan().SequenceEqual(second.AsSpan()))
            {
                throw new InvalidOperationException("two Genesis generations were not byte-identical");
            }

            var syntax = DagLedgerLoader.Load(first.AsSpan()) switch
            {
                DagLedgerLoadOutcome.Loaded loaded => loaded.Syntax,
                DagLedgerLoadOutcome.Invalid invalid => throw new InvalidOperationException(invalid.Message),
                _ => throw new InvalidOperationException("unknown ledger load outcome"),
            };
            var scanned = FrozenLedger.ScanReferences(syntax) switch
            {
                FrozenLedgerReferenceScanOutcome.Accepted accepted => accepted.References,
                FrozenLedgerReferenceScanOutcome.Rejected rejected => throw new InvalidOperationException(rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger reference scan outcome"),
            };
            var trustedReferences = repository.ValidateFrozenReferences(scanned);
            var ledger = FrozenLedger.ValidateGenesis(syntax, catalog, trustedReferences) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            var outputPath = Path.Combine(
                repositoryRoot,
                FrozenLedgerChangeClassifier.LedgerPath.Replace('/', Path.DirectorySeparatorChar));
            if (File.Exists(outputPath))
            {
                if (!File.ReadAllBytes(outputPath).AsSpan().SequenceEqual(first.AsSpan()))
                {
                    throw new InvalidOperationException(
                        "events.jsonl already exists with different bytes; Genesis is append-only");
                }
            }
            else
            {
                Directory.CreateDirectory(Path.GetDirectoryName(outputPath)
                    ?? throw new InvalidOperationException("ledger output has no parent directory"));
                File.WriteAllBytes(outputPath, first.AsSpan());
            }

            return new CommandResult(
                true,
                $"LEDGER_GENESIS events={ledger.Events.Length} "
                + $"closed_modules={ledger.ActiveFrozenNodes.Length} "
                + $"head={ledger.HeadHash} corpus={ledger.CorpusRoot}\n",
                string.Empty);
        }
        catch (Exception exception) when (exception is IOException or InvalidOperationException or UnauthorizedAccessException)
        {
            return new CommandResult(
                false,
                string.Empty,
                "LEDGER_GENESIS_FAILED " + exception.Message + "\n");
        }
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static string GitBlobOid(ReadOnlySpan<byte> bytes, HashAlgorithmName algorithm)
    {
        using var hash = IncrementalHash.CreateHash(algorithm);
        hash.AppendData(Encoding.ASCII.GetBytes($"blob {bytes.Length}\0"));
        hash.AppendData(bytes);
        var prefix = algorithm == HashAlgorithmName.SHA1 ? "git-sha1:" : "git-sha256:";
        return prefix + Convert.ToHexStringLower(hash.GetHashAndReset());
    }
}
