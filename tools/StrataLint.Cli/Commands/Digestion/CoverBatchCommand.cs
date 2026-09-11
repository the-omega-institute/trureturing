using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.Scribe.Documents;

namespace StrataLint.Cli;

internal static partial class CoverBatchCommand
{
    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier? scribeEmissionVerifier,
        DateTimeOffset recordedAtUtc,
        IReadOnlyList<string> arguments,
        Func<CommandResult>? emit = null,
        Func<RawRepositorySnapshot>? readInputs = null,
        Assembly? documentsAssembly = null)
    {
        BatchArguments options;
        try
        {
            options = Parse(repositoryRoot, arguments);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(false, string.Empty, $"COVER_BATCH_INPUT_INVALID {exception.Message}\n", 2);
        }

        using var reportBundle = (leanReportSource as PrecomputedLeanReportSource)?.Capture();
        CoverAtomCommand.Session session;
        BatchPlan plan;
        try
        {
            if (scribeEmissionVerifier is null)
                throw new InvalidOperationException("Scribe emission verifier is unavailable");
            session = new CoverAtomCommand.Session(repositoryRoot, repository, reportBundle is null ? leanReportSource : reportBundle,
                scribeEmissionVerifier, recordedAtUtc, options.BaseRevision, options.Items[0].Gids[0]);
            plan = Plan(options.Items, session.Document);
            var expected = Inputs(session.CurrentRaw);
            readInputs ??= () => GitRepositorySnapshotReader.ReadCurrent(repositoryRoot,
                static path => !IngestCommand.IsLedgerPath(path));
            session.ValidateInputs = () => RequireSameInputs(expected, Inputs(readInputs()));
        }
        catch (BatchInputException exception)
        {
            return new(false, string.Empty, $"COVER_BATCH_INPUT_INVALID {exception.Message}\n", 2);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            var output = new StringBuilder();
            foreach (var item in options.Items)
                Render(output, item, "blocked", "shared context unavailable: " + exception.Message);
            return new(false, output.ToString(), $"COVER_BATCH_ABORTED {exception.Message}\n", 1);
        }

        var results = new StringBuilder();
        var failures = new Dictionary<string, string>(StringComparer.Ordinal);
        string? aborted = null;
        var successful = true;
        foreach (var atomId in plan.Order)
        {
            var dependencyFailure = plan.Children[atomId].Select(child => failures.GetValueOrDefault(child))
                .FirstOrDefault(reason => reason is not null);
            if (!plan.Items.TryGetValue(atomId, out var item))
            {
                if (dependencyFailure is not null) failures[atomId] = dependencyFailure;
                continue;
            }

            if (aborted is not null || dependencyFailure is not null)
            {
                successful = false;
                var reason = aborted is not null ? "batch aborted: " + aborted : "dependency failed: " + dependencyFailure;
                failures[atomId] = dependencyFailure ?? atomId;
                Render(results, item, "blocked", reason);
                continue;
            }

            var existing = session.Document.RequireDigestionEntries()
                .Where(entry => entry.AtomId == atomId).ToArray();
            var alreadyApplied = existing.Length == 1 && item.Gids.All(existing[0].CoverageGids.Contains);
            var result = session.Apply(atomId, item.Gids);
            var reasonText = result.Error.Trim();
            if (!result.Success)
            {
                successful = false;
                failures[atomId] = atomId;
                if (!session.Invalidated)
                {
                    try { session.RequireUnchanged(); }
                    catch (Exception exception) when (exception is not OutOfMemoryException)
                    {
                        reasonText += "; " + exception.Message;
                    }
                }
                if (session.Invalidated) aborted = reasonText;
            }
            Render(results, item, result.Success ? alreadyApplied ? "already_applied" : "applied" : "failed",
                result.Success ? alreadyApplied ? "coverage bindings validated" : "coverage committed" : reasonText);
        }

        if (aborted is not null)
            return new(false, results.ToString(), $"COVER_BATCH_ABORTED {aborted}\n", 1);

        CommandResult emission;
        try
        {
            session.RequireUnchanged();
            emission = (emit ?? (() => Emit(repositoryRoot, session, reportBundle,
                documentsAssembly ?? typeof(DocumentAssembly).Assembly)))();
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            emission = new(false, string.Empty, $"COVER_BATCH_EMIT_FAILED {exception.Message}\n");
        }
        successful &= emission.Success;
        return new(successful, results + emission.Output, emission.Error, successful ? 0 : 1);
    }

    private static Dictionary<string, RawRepositoryEntry> Inputs(RawRepositorySnapshot snapshot) =>
        snapshot.Entries.Where(static entry => !IngestCommand.IsLedgerPath(entry.Path))
            .ToDictionary(static entry => entry.Path, StringComparer.Ordinal);

    private static void RequireSameInputs(IReadOnlyDictionary<string, RawRepositoryEntry> expected,
        IReadOnlyDictionary<string, RawRepositoryEntry> actual, Func<string, bool>? allowChange = null)
    {
        var mismatch = expected.Keys.Union(actual.Keys, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal).FirstOrDefault(path =>
                (!expected.TryGetValue(path, out var before) || !actual.TryGetValue(path, out var after)
                    || !before.Bytes.AsSpan().SequenceEqual(after.Bytes.AsSpan()))
                && allowChange?.Invoke(path) is not true);
        if (mismatch is not null)
            throw new InvalidOperationException($"shared cover context changed: {mismatch}");
    }

    private static void Render(StringBuilder output, BatchItem item, string status, string reason) =>
        output.Append("COVER_BATCH ").Append(JsonSerializer.Serialize(new
        {
            atom_id = item.AtomId,
            status,
            lines = item.Lines,
            reason,
        })).Append('\n');

    private static CommandResult Emit(string root, CoverAtomCommand.Session session,
        PrecomputedLeanReportSource.CapturedBundle? reportBundle, Assembly documentsAssembly)
    {
        if (reportBundle is null)
            throw new InvalidOperationException("final emission requires a precomputed Lean report bundle");
        reportBundle.ValidateForEmission();
        session.RequireUnchanged();
        var output = new StringWriter();
        var error = new StringWriter();
        // Match scribe.sh's ordered producers while retaining the validated batch inputs.
        var exit = ScribeEmitter.Emit(documentsAssembly, root, false, output, error, session.Report,
            validateRepository: true, session.FrozenState, session.FrozenStatements);
        if (exit == 0) exit = ValuesEmitter.Emit(root, false, output, error);
        if (exit == 0) exit = FileMapEmitter.Emit(root, false, output, error);
        if (exit != 0) return new(false, output.ToString(), error.ToString());
        var dag = DagRenderCommand.Run(root, new(ReadEmittedSnapshot(root, session), session.Lean, session.Report), false,
            documentsAssembly);
        output.Write(dag.Output);
        error.Write(dag.Error);
        try
        {
            ReadEmittedInputs(root, session);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            error.Write($"COVER_BATCH_EMIT_FAILED {exception.Message}\n");
            return new(false, output.ToString(), error.ToString());
        }
        return new(dag.Success, output.ToString(), error.ToString());
    }

    private static RepositorySnapshot ReadEmittedSnapshot(string root, CoverAtomCommand.Session session) =>
        SnapshotDecoder.Decode(ReadEmittedInputs(root, session)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(failure.Message),
        };

    private static RawRepositorySnapshot ReadEmittedInputs(string root, CoverAtomCommand.Session session)
    {
        var manifestFile = session.Current.Files[RepoPath.CreateKnown(FileMapLoader.RelativePath)];
        var manifest = FileMapLoader.Parse(manifestFile.RawBytes.AsSpan(), FileMapLoader.RelativePath);
        var raw = GitRepositorySnapshotReader.ReadCurrent(root);
        // Generated path membership affects DAG provenance; all authoritative inputs must still match.
        RequireSameInputs(Inputs(session.CurrentRaw), Inputs(raw),
            path => manifest.Match(path) is [{ Kind: FileMapKind.Generated }]);
        IngestCommand.RequireLedgerUnchanged(root, session.CurrentRaw);
        return raw;
    }
}
