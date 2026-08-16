using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal enum FrontierCandidateClassification
{
    MathematicalOpen,
    GovernanceTicket,
    OutsideFrontier,
    NotOpen,
    Unaddressed,
}

internal sealed record TheoryCandidate(
    string CandidateId,
    string SourceKind,
    string SourceRef,
    string ContentSha256,
    string DownstreamLane,
    string? ProblemText);

internal static class TheoryCandidatesCommand
{
    private const string FrontierPrefix = "D5/X_Frontier/";

    internal static CommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var ownerOverride = ParseArguments(arguments);
            var truth = DagLedgerCommandPreparation.BuildTruth(repository, leanReportSource);
            var mission = MissionFileLoader.Load(truth.Snapshot) switch
            {
                MissionLoadOutcome.Loaded loaded => loaded.Policy,
                MissionLoadOutcome.Invalid invalid => throw new FormatException(invalid.Error.Message),
                _ => throw new InvalidOperationException("MISSION loader returned an unsupported outcome"),
            };
            var ticketModules = BackfillInventoryLoader.DeriveTickets(truth.Snapshot)
                .Select(static ticket => ticket.Gid)
                .ToHashSet(StringComparer.Ordinal);
            var frontierCandidates = truth.Dag.Nodes
                .Where(node => ClassifyFrontier(node, ticketModules)
                    == FrontierCandidateClassification.MathematicalOpen)
                .Select(node => FrontierCandidate(node, truth.Snapshot))
                .ToArray();

            var digestion = DigestionStatusEvaluator.Evaluate(
                BackfillInventoryLoader.Load(truth.Snapshot),
                truth.Snapshot,
                truth.Lean,
                scribeEmissionVerifier.Verify(truth.Report));
            if (digestion.Findings.Length > 0)
            {
                throw new InvalidOperationException(
                    "digestion evaluation rejected the current snapshot: "
                    + string.Join("; ", digestion.Findings));
            }

            var atomCandidates = digestion.Entries
                .Where(static entry =>
                    entry.DerivedStatus.Migration == DigestionMigrationState.Residual
                    && entry.DerivedStatus.Truth == DigestionTruthState.Open)
                .Select(static entry => new TheoryCandidate(
                    "atom/" + entry.Entry.AtomId,
                    "digestion_atom",
                    entry.Entry.AtomId,
                    entry.Entry.CasRef,
                    "codex-formalize",
                    null));
            var output = TheoryCandidateProjection.Render(
                TruthGraphSnapshotIdentity.Compute(truth.Snapshot),
                mission,
                frontierCandidates.Concat(atomCandidates).ToArray(),
                ownerOverride);
            return new CommandResult(true, output, string.Empty);
        }
        catch (Exception exception) when (
            exception is FormatException
                or InvalidOperationException
                or IOException
                or ArgumentException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"THEORY_CANDIDATES_INVALID {exception.Message}\n");
        }
    }

    internal static FrontierCandidateClassification ClassifyFrontier(
        TruthNode node,
        IReadOnlySet<string> ticketModules)
    {
        ArgumentNullException.ThrowIfNull(node);
        ArgumentNullException.ThrowIfNull(ticketModules);
        if (node.State != TruthState.Open)
        {
            return FrontierCandidateClassification.NotOpen;
        }

        if (!node.RepoPath.Value.StartsWith(FrontierPrefix, StringComparison.Ordinal)
            || !node.RepoPath.Value.EndsWith(".lean", StringComparison.Ordinal))
        {
            return FrontierCandidateClassification.OutsideFrontier;
        }

        if (node.Gid is null)
        {
            return FrontierCandidateClassification.Unaddressed;
        }

        return ticketModules.Contains(node.Gid.Value)
            ? FrontierCandidateClassification.GovernanceTicket
            : FrontierCandidateClassification.MathematicalOpen;
    }

    private static TheoryCandidate FrontierCandidate(
        TruthNode node,
        RepositorySnapshot snapshot)
    {
        var gid = node.Gid
            ?? throw new InvalidOperationException(
                $"mathematical Frontier node has no canonical GID: {node.RepoPath.Value}");
        var file = snapshot.Files[node.RepoPath];
        return new TheoryCandidate(
            "frontier/" + gid.Value,
            "frontier_open",
            gid.Value,
            "sha256:" + Convert.ToHexStringLower(SHA256.HashData(file.RawBytes.AsSpan())),
            "prover",
            null);
    }

    private static string? ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 0)
        {
            return null;
        }

        if (arguments.Count == 2
            && arguments[0] == "--owner-override"
            && !string.IsNullOrWhiteSpace(arguments[1]))
        {
            return arguments[1];
        }

        throw new ArgumentException(
            "USAGE: StrataLint theory-candidates [--owner-override OPEN_PROBLEM]");
    }
}

internal static class TheoryCandidateProjection
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };

    internal static string Render(
        string inputSnapshotSha256,
        MissionPolicy mission,
        IReadOnlyList<TheoryCandidate> repositoryCandidates,
        string? ownerOverride)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(inputSnapshotSha256);
        ArgumentNullException.ThrowIfNull(mission);
        ArgumentNullException.ThrowIfNull(repositoryCandidates);
        if (mission.Selection.OrderKind != WorthSelectionOrder.BootstrapEligibilityOrder)
        {
            throw new InvalidOperationException(
                "bootstrap selection is unavailable under the current MISSION policy");
        }

        var candidates = repositoryCandidates.ToList();
        TheoryCandidate? ownerCandidate = null;
        if (ownerOverride is not null)
        {
            var problemBytes = StrictUtf8.GetBytes(ownerOverride);
            var contentSha256 = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(problemBytes));
            ownerCandidate = new TheoryCandidate(
                "owner_override/" + contentSha256["sha256:".Length..],
                "owner_override",
                contentSha256,
                contentSha256,
                "prover",
                ownerOverride);
            candidates.Add(ownerCandidate);
        }

        var ordered = candidates
            .OrderBy(static candidate => candidate.CandidateId, StringComparer.Ordinal)
            .ToImmutableArray();
        if (ordered.Select(static candidate => candidate.CandidateId)
            .Distinct(StringComparer.Ordinal).Count() != ordered.Length)
        {
            throw new InvalidOperationException("candidate ids must be unique");
        }

        var candidateElement = JsonSerializer.SerializeToElement(ordered, JsonOptions);
        var candidateSetSha256 = CandidateSetSha256(candidateElement);
        var selected = ownerCandidate?.CandidateId ?? ordered.FirstOrDefault()?.CandidateId;
        var material = new
        {
            schema = "stratalint-theory-candidates-v1",
            selection_receipt = new
            {
                input_snapshot_sha256 = inputSnapshotSha256,
                candidate_set_sha256 = candidateSetSha256,
                ordering_version = "theory-candidates-bootstrap-v1",
                order_kind = MissionFileLoader.SelectionName(mission.Selection.OrderKind),
                tie_break = mission.Selection.TieBreak,
                selection_mode = ownerCandidate is null ? "bootstrap_order" : "owner_override",
                selected_candidate_id = selected,
            },
            candidates = ordered,
        };
        return StrictUtf8.GetString(
            StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(material, JsonOptions)).AsSpan());
    }

    private static string CandidateSetSha256(JsonElement candidates)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        hash.AppendData(StrictUtf8.GetBytes("theory-candidate-set-v1\0"));
        hash.AppendData(StructuredCanonicalWriter.WriteJson(candidates).AsSpan());
        return "sha256:" + Convert.ToHexStringLower(hash.GetHashAndReset());
    }
}
