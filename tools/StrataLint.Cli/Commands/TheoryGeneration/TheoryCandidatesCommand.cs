using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal enum FrontierCandidateClassification
{
    DeclarationReadyMathematicalOpen,
    MathematicalNotYetStated,
    Governance,
    Unknown,
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
    string? ProblemText,
    // The type-only statement address a V2 Frontier contract copies into
    // exact_statement.statement_sha256; issued only for declaration-ready
    // candidates, where the elaborated type exists.
    [property: System.Text.Json.Serialization.JsonIgnore(
        Condition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull)]
    string? StatementTypeSha256 = null);

internal sealed record OwnerOverrideInput(
    ImmutableArray<byte> RawBytes,
    string ProblemText,
    string ContentSha256);

internal sealed record WithheldTheoryCandidate(
    string CandidateId,
    string SourceKind,
    string SourceRef,
    string WithholdReason);

internal static class TheoryCandidatesCommand
{
    private const string FrontierPrefix = "D5/X_Frontier/";
    private const string ImplementationPath =
        "tools/StrataLint.Cli/Commands/TheoryGeneration/TheoryCandidatesCommand.cs";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

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
            var changes = repository.ReadCurrentChanges();
            var scope = DigestionEvaluationScopes.ForChanges(changes, ImplementationPath);
            var mission = MissionFileLoader.Load(truth.Snapshot) switch
            {
                MissionLoadOutcome.Loaded loaded => loaded.Policy,
                MissionLoadOutcome.Invalid invalid => throw new FormatException(invalid.Error.Message),
                _ => throw new InvalidOperationException("MISSION loader returned an unsupported outcome"),
            };
            var eligibility = mission.FrontierEligibility.ToDictionary(
                static entry => entry.SourceRef,
                static entry => entry.Kind,
                StringComparer.Ordinal);
            var states = LeanTruthStates.Resolve(truth.Snapshot, truth.Lean);
            var classifiedFrontier = states
                .OrderBy(static item => item.Key.Value, StringComparer.Ordinal)
                .Select(item =>
                {
                    RepositoryPathPolicy.TryResolve(item.Key, out var gid);
                    var node = new FrontierStateNode(item.Key, gid, item.Value);
                    return (Node: node, Classification: ClassifyFrontier(node, eligibility));
                })
                .Where(static item => item.Classification is not (
                    FrontierCandidateClassification.OutsideFrontier
                    or FrontierCandidateClassification.NotOpen))
                .ToArray();
            var unclassified = classifiedFrontier
                .Where(static item => item.Classification is
                    FrontierCandidateClassification.Unknown
                    or FrontierCandidateClassification.Unaddressed)
                .Select(static item => item.Node.RepoPath.Value)
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (unclassified.Length > 0)
            {
                throw new InvalidOperationException(
                    "unclassified Frontier source(s): " + string.Join(", ", unclassified));
            }

            var frontierCandidates = classifiedFrontier
                .Where(static item => item.Classification is
                    FrontierCandidateClassification.DeclarationReadyMathematicalOpen
                    or FrontierCandidateClassification.MathematicalNotYetStated)
                .SelectMany(item => FrontierCandidates(
                    item.Node,
                    item.Classification,
                    truth.Snapshot,
                    truth.Report))
                .ToArray();

            var document = BackfillInventoryLoader.Load(truth.Snapshot, scope, changes);
            // A read-only projection of the current tree is its own baseline. Without one the
            // aligner cannot recognise a prior generation that the ledger has already
            // acknowledged as superseded, so it classifies that entry `Rejected`, structural
            // alignment fails, and the entry derives `partial` against a handwritten
            // `absorbed` -- a disagreement about nothing. Measured on dev 36baebe09: this call
            // reported 55 such entries while `digest-status --base HEAD`, which differs only by
            // passing a baseline, reported 0 on the same tree and the same Lean report (#3354).
            var baselineDocument = BackfillInventoryLoader.LoadBaseline(truth.Snapshot);
            var ruleImplementationChanged = BaseFactImpact.RuleImplementationChanged(changes);
            bool IsBaseFactAffected(string path) =>
                BaseFactImpact.IsAffected(changes, ruleImplementationChanged, path);
            var digestion = DigestionStatusEvaluator.Evaluate(
                scope,
                document,
                truth.Snapshot,
                truth.Lean,
                scribeEmissionVerifier.Verify(truth.Snapshot, truth.Report),
                baselineDocument,
                baselineSnapshot: truth.Snapshot,
                casEvaluation: DigestionCasStore.Evaluate(
                    document,
                    truth.Snapshot,
                    DigestionEvaluationScopes.ResolveChanges(scope, changes),
                    IsBaseFactAffected),
                changes: changes,
                isBaseFactAffected: IsBaseFactAffected,
                truthStates: states);
            if (digestion.HasReceiptIntegrityFailure)
            {
                throw new InvalidOperationException(
                    "digestion evaluation rejected the current snapshot: "
                    + string.Join("; ", digestion.ReceiptIntegrityFailureReasons));
            }

            var atomSelections = digestion.Entries
                .Where(static entry =>
                    entry.DerivedStatus.Migration == DigestionMigrationState.Residual
                    && entry.DerivedStatus.Truth == DigestionTruthState.Open)
                .Select(static entry => new
                {
                    Evaluation = entry,
                    Selection = DigestionCoverDispositionSelector.Classify(
                        entry.Entry,
                        retryDispositions: false),
                })
                .ToArray();
            var atomCandidates = atomSelections
                .Where(static item => item.Selection == DigestionCoverDispositionSelection.Available)
                .Select(static item => new TheoryCandidate(
                    "atom/" + item.Evaluation.Entry.AtomId,
                    "digestion_atom",
                    item.Evaluation.Entry.AtomId,
                    item.Evaluation.Entry.CasRef,
                    "codex-formalize",
                    null));
            var withheldAtoms = atomSelections
                .Where(static item => item.Selection == DigestionCoverDispositionSelection.Withheld)
                .Select(static item => new WithheldTheoryCandidate(
                    "atom/" + item.Evaluation.Entry.AtomId,
                    "digestion_atom",
                    item.Evaluation.Entry.AtomId,
                    DigestionCoverDispositionSelector.WithholdReason))
                .ToArray();
            var output = TheoryCandidateProjection.Render(
                SnapshotContentDigest.Compute(truth.Snapshot),
                RawLeanReportArtifact.ContentAddress(
                    RawLeanReportArtifact.Write(truth.Snapshot, truth.Report).AsSpan()),
                mission,
                frontierCandidates.Concat(atomCandidates).ToArray(),
                withheldAtoms,
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
        FrontierStateNode node,
        IReadOnlyDictionary<string, FrontierEligibilityKind> eligibility)
    {
        ArgumentNullException.ThrowIfNull(node);
        ArgumentNullException.ThrowIfNull(eligibility);
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

        if (!eligibility.TryGetValue(node.Gid.Value, out var kind))
        {
            return FrontierCandidateClassification.Unknown;
        }

        return kind switch
        {
            FrontierEligibilityKind.DeclarationReadyMathematicalOpen =>
                FrontierCandidateClassification.DeclarationReadyMathematicalOpen,
            FrontierEligibilityKind.MathematicalNotYetStated =>
                FrontierCandidateClassification.MathematicalNotYetStated,
            FrontierEligibilityKind.Governance => FrontierCandidateClassification.Governance,
            FrontierEligibilityKind.Retired => FrontierCandidateClassification.NotOpen,
            FrontierEligibilityKind.Unknown => FrontierCandidateClassification.Unknown,
            _ => throw new InvalidOperationException("unsupported Frontier eligibility kind"),
        };
    }

    private static IReadOnlyList<TheoryCandidate> FrontierCandidates(
        FrontierStateNode node,
        FrontierCandidateClassification classification,
        RepositorySnapshot snapshot,
        LeanAxiomReport report)
    {
        var gid = node.Gid
            ?? throw new InvalidOperationException(
                $"mathematical Frontier node has no canonical GID: {node.RepoPath.Value}");
        var file = snapshot.Files[node.RepoPath];
        if (classification == FrontierCandidateClassification.MathematicalNotYetStated)
        {
            return
            [
                new TheoryCandidate(
                    "frontier/" + gid.Value,
                    "frontier_problem",
                    gid.Value,
                    "sha256:" + Convert.ToHexStringLower(SHA256.HashData(file.RawBytes.AsSpan())),
                    "theorist",
                    null),
            ];
        }

        if (classification != FrontierCandidateClassification.DeclarationReadyMathematicalOpen)
        {
            throw new InvalidOperationException(
                $"non-mathematical Frontier classification cannot become a candidate: {classification}");
        }

        if (!report.Files.TryGetValue(node.RepoPath, out var fileReport))
        {
            throw new InvalidOperationException(
                $"Lean report has no declaration-ready Frontier source: {node.RepoPath.Value}");
        }

        var statementIds = CanonicalStatementWriter.DeclarationStatementIds(node.RepoPath, fileReport)
            .ToDictionary(
                static statement => (statement.DeclarationNameKey, statement.Kind),
                static statement => statement.StatementId.Value);
        var candidates = fileReport.Declarations
            .Where(IsOpenProposition)
            .Select(declaration =>
            {
                var declarationGid = DeclarationGid(gid, node.RepoPath, declaration);
                if (!statementIds.TryGetValue((declaration.NameKey, declaration.Kind), out var statementId))
                {
                    throw new InvalidOperationException(
                        $"Lean report declaration has no canonical statement address: {declarationGid}");
                }

                return new TheoryCandidate(
                    "frontier/" + declarationGid,
                    "frontier_declaration_ready",
                    declarationGid,
                    statementId,
                    "prover",
                    null,
                    CanonicalStatementWriter.StatementTypeAddress(declaration));
            })
            .OrderBy(static candidate => candidate.CandidateId, StringComparer.Ordinal)
            .ToArray();
        if (candidates.Length == 0)
        {
            throw new InvalidOperationException(
                $"declaration-ready Frontier source has no report-addressed open proposition: {gid.Value}");
        }

        return candidates;
    }

    private static bool IsOpenProposition(LeanDeclaration declaration)
    {
        if (!declaration.IncludeInStatement)
        {
            return false;
        }

        if (string.Equals(declaration.Kind, "theorem", StringComparison.Ordinal))
        {
            return declaration.Axioms.Contains("sorryAx", StringComparer.Ordinal);
        }

        return string.Equals(declaration.Kind, "def", StringComparison.Ordinal)
            && StatementV1Decoder.Decode(declaration.LoadTypeRepresentation()).Type
                is LeanExpr.Sort { Level: LeanLevel.Zero };
    }

    private static string DeclarationGid(Gid moduleGid, RepoPath modulePath, LeanDeclaration declaration)
    {
        var qualifiedPrefix = moduleGid.Value.Replace('/', '.') + ".";
        if (!declaration.Name.StartsWith(qualifiedPrefix, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"Lean report declaration is outside its Frontier module: {declaration.Name}");
        }

        var selector = declaration.Name[qualifiedPrefix.Length..];
        var value = moduleGid.Value + "." + selector;
        if (selector.Contains('.', StringComparison.Ordinal)
            || !Gid.TryParse(value, out var declarationGid)
            || declarationGid.Path != modulePath)
        {
            throw new InvalidOperationException(
                $"Lean report declaration has no canonical declaration GID: {declaration.Name}");
        }

        return declarationGid.Value;
    }

    private static OwnerOverrideInput? ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 0)
        {
            return null;
        }

        if (arguments.Count == 2
            && arguments[0] == "--owner-override-file"
            && !string.IsNullOrWhiteSpace(arguments[1]))
        {
            var rawBytes = ImmutableArray.CreateRange(File.ReadAllBytes(arguments[1]));
            var contentSha256 = "sha256:"
                + Convert.ToHexStringLower(SHA256.HashData(rawBytes.AsSpan()));
            string problemText;
            try
            {
                problemText = StrictUtf8.GetString(rawBytes.AsSpan());
            }
            catch (DecoderFallbackException exception)
            {
                throw new FormatException("owner override must be strict UTF-8", exception);
            }

            if (string.IsNullOrWhiteSpace(problemText))
            {
                throw new FormatException("owner override must contain a non-whitespace open problem");
            }

            return new OwnerOverrideInput(rawBytes, problemText, contentSha256);
        }

        throw new ArgumentException(
            "USAGE: StrataLint theory-candidates [--owner-override-file PATH]");
    }
}

internal sealed record FrontierStateNode(RepoPath RepoPath, Gid? Gid, TruthState State);

internal static class TheoryCandidateProjection
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };

    internal static string Render(
        string inputSnapshotSha256,
        string leanReportSha256,
        MissionPolicy mission,
        IReadOnlyList<TheoryCandidate> repositoryCandidates,
        IReadOnlyList<WithheldTheoryCandidate> withheldCandidates,
        OwnerOverrideInput? ownerOverride)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(inputSnapshotSha256);
        ArgumentException.ThrowIfNullOrWhiteSpace(leanReportSha256);
        ArgumentNullException.ThrowIfNull(mission);
        ArgumentNullException.ThrowIfNull(repositoryCandidates);
        ArgumentNullException.ThrowIfNull(withheldCandidates);
        if (mission.Selection.OrderKind != WorthSelectionOrder.BootstrapEligibilityOrder)
        {
            throw new InvalidOperationException(
                "bootstrap selection is unavailable under the current MISSION policy");
        }

        var candidates = repositoryCandidates.ToList();
        TheoryCandidate? ownerCandidate = null;
        if (ownerOverride is not null)
        {
            ownerCandidate = new TheoryCandidate(
                "owner_override/" + ownerOverride.ContentSha256["sha256:".Length..],
                "owner_override",
                ownerOverride.ContentSha256,
                ownerOverride.ContentSha256,
                "theorist",
                ownerOverride.ProblemText);
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
        var withheld = withheldCandidates
            .OrderBy(static candidate => candidate.CandidateId, StringComparer.Ordinal)
            .ToImmutableArray();
        var candidateSetSha256 = CandidateSetSha256(candidateElement);
        var selected = ownerCandidate?.CandidateId ?? ordered.FirstOrDefault()?.CandidateId;
        var material = new
        {
            schema = "stratalint-theory-candidates-v1",
            selection_receipt = new
            {
                input_snapshot_sha256 = inputSnapshotSha256,
                lean_report_sha256 = leanReportSha256,
                candidate_set_sha256 = candidateSetSha256,
                ordering_version = "theory-candidates-bootstrap-v1",
                order_kind = MissionFileLoader.SelectionName(mission.Selection.OrderKind),
                tie_break = mission.Selection.TieBreak,
                selection_mode = ownerCandidate is null ? "bootstrap_order" : "owner_override",
                selected_candidate_id = selected,
            },
            withheld,
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
