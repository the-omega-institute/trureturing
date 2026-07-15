using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ConservativeCorpusEvaluator
{
    private const string Schema = "stratalint-conservative-corpus-v1";

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        PropertyNameCaseInsensitive = false,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
    };

    internal static ConservativeHarnessRun Evaluate(
        ReadOnlySpan<byte> canonicalCorpus,
        string harnessRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(harnessRoot);
        var corpus = Read(canonicalCorpus);
        var cases = corpus.Cases
            .Select(item => Evaluate(item, corpus.Objects))
            .ToImmutableArray();
        var contractCases = corpus.Cases
            .Where(static item => item.ContractEpoch is not null)
            .Select(static item => ContractEpochCorpusEvaluator.Evaluate(
                item.CaseId,
                item.ContractEpoch!))
            .ToImmutableArray();
        var activeRules = RuleCatalog.Default.Descriptors
            .Where(static descriptor => descriptor.Lifecycle is RuleLifecycle.Active)
            .Select(static descriptor => descriptor.Id.Value)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        return new ConservativeHarnessRun(harnessRoot, activeRules, cases)
        {
            ContractCases = contractCases,
        };
    }

    private static ParsedCorpus Read(ReadOnlySpan<byte> bytes)
    {
        string text;
        try
        {
            text = new UTF8Encoding(false, true).GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("conservative corpus must be strict UTF-8", exception);
        }

        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException("conservative corpus is not valid JSON", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException("conservative corpus bytes are not canonical JSON");
        }

        ConservativeCorpusDocument document;
        try
        {
            document = JsonSerializer.Deserialize<ConservativeCorpusDocument>(text, JsonOptions)
                ?? throw new FormatException("conservative corpus document is null");
        }
        catch (JsonException exception)
        {
            throw new FormatException("conservative corpus schema is invalid", exception);
        }

        if (!string.Equals(document.Schema, Schema, StringComparison.Ordinal)
            || document.Objects.IsDefaultOrEmpty
            || document.Cases.IsDefaultOrEmpty)
        {
            throw new FormatException("conservative corpus schema or required arrays are invalid");
        }

        RequireStrictOrder(document.Objects.Select(static item => item.Root), "object roots");
        var objects = ImmutableDictionary.CreateBuilder<string, ImmutableArray<byte>>(StringComparer.Ordinal);
        foreach (var item in document.Objects)
        {
            byte[] raw;
            try
            {
                raw = Convert.FromBase64String(item.BytesBase64);
            }
            catch (FormatException exception)
            {
                throw new FormatException($"corpus object {item.Root} is not base64", exception);
            }

            if (!string.Equals(
                item.Root,
                GoldenCorpusMaterializer.ContentRoot(raw),
                StringComparison.Ordinal))
            {
                throw new FormatException($"corpus object root does not match bytes: {item.Root}");
            }

            if (!objects.TryAdd(item.Root, ImmutableArray.CreateRange(raw)))
            {
                throw new FormatException($"duplicate corpus object root: {item.Root}");
            }
        }

        RequireStrictOrder(document.Cases.Select(static item => item.CaseId), "case ids");
        foreach (var item in document.Cases)
        {
            ValidateCase(item, objects);
        }

        return new ParsedCorpus(document.Cases, objects.ToImmutable());
    }

    private static void ValidateCase(
        ConservativeCorpusCase item,
        IReadOnlyDictionary<string, ImmutableArray<byte>> objects)
    {
        if (string.IsNullOrWhiteSpace(item.CaseId)
            || string.IsNullOrWhiteSpace(item.CaseRoot)
            || item.CurrentFiles.IsDefaultOrEmpty
            || item.BaselineFiles.IsDefaultOrEmpty
            || item.CurrentLean.IsDefault
            || item.BaselineLean.IsDefault
            || item.Changes.IsDefaultOrEmpty)
        {
            throw new FormatException("conservative corpus case has missing required fields");
        }

        if (!string.Equals(
            item.CaseRoot,
            GoldenCorpusMaterializer.CaseRoot(item),
            StringComparison.Ordinal))
        {
            throw new FormatException($"conservative corpus case root mismatch: {item.CaseId}");
        }

        ValidateFiles(item.CurrentFiles, objects, item.CaseId, "current");
        ValidateFiles(item.BaselineFiles, objects, item.CaseId, "baseline");
        ValidateLean(item.CurrentLean, item.CaseId, "current");
        ValidateLean(item.BaselineLean, item.CaseId, "baseline");
        RequireStrictOrder(item.Changes, $"{item.CaseId} changes");
        if (item.Changes.Any(static path => !RepoPath.TryCreate(path, out _)))
        {
            throw new FormatException($"conservative corpus case has invalid changed path: {item.CaseId}");
        }

        ContractEpochCorpusEvaluator.Validate(item.CaseId, item.ContractEpoch);
    }

    private static void ValidateFiles(
        ImmutableArray<ConservativeCorpusFile> files,
        IReadOnlyDictionary<string, ImmutableArray<byte>> objects,
        string caseId,
        string side)
    {
        RequireStrictOrder(files.Select(static item => item.Path), $"{caseId} {side} files");
        foreach (var file in files)
        {
            if (!RepoPath.TryCreate(file.Path, out _) || !objects.ContainsKey(file.ObjectRoot))
            {
                throw new FormatException(
                    $"conservative corpus case has invalid {side} file reference: {caseId}/{file.Path}");
            }
        }
    }

    private static void ValidateLean(
        ImmutableArray<ConservativeCorpusLeanFile> files,
        string caseId,
        string side)
    {
        RequireStrictOrder(files.Select(static item => item.Path), $"{caseId} {side} Lean files");
        foreach (var file in files)
        {
            if (!RepoPath.TryCreate(file.Path, out _)
                || file.Imports.IsDefault
                || file.Declarations.IsDefault
                || file.Declarations.Any(static declaration =>
                    string.IsNullOrWhiteSpace(declaration.Name)
                    || string.IsNullOrWhiteSpace(declaration.NameKey)
                    || string.IsNullOrWhiteSpace(declaration.Kind)
                    || string.IsNullOrWhiteSpace(declaration.TypeRepresentation)
                    || declaration.Axioms.IsDefault))
            {
                throw new FormatException(
                    $"conservative corpus case has malformed {side} Lean report: {caseId}/{file.Path}");
            }
        }
    }

    private static ConservativeCaseResult Evaluate(
        ConservativeCorpusCase source,
        IReadOnlyDictionary<string, ImmutableArray<byte>> objects)
    {
        var current = Decode(source.CurrentFiles, objects);
        var baseline = Decode(source.BaselineFiles, objects);
        if (!current.TryGetFile("Meta/registry.yaml", out var registryFile)
            || !current.TryGetFile("Meta/domains.yaml", out var domainsFile))
        {
            throw new FormatException($"conservative corpus case lacks policy files: {source.CaseId}");
        }

        var changes = RawChangeSet.Create(source.Changes);
        var bootstrap = BootstrapGate.Evaluate(changes);
        var evaluation = SnapshotAdmissionCore.Evaluate(
            current,
            baseline,
            LeanAxiomReport.Create(Reports(source.CurrentLean)),
            LeanAxiomReport.Create(Reports(source.BaselineLean)),
            changes,
            bootstrap,
            verifiedScribeEmissions: null);
        var diagnostics = evaluation.Outcome switch
        {
            AdmissionOutcome.Admitted => ImmutableArray<Diagnostic>.Empty,
            AdmissionOutcome.ProtectedSurfaceChange protectedChange =>
                protectedChange.Sl022Diagnostics,
            AdmissionOutcome.RuleRejected rejected => rejected.Diagnostics,
            AdmissionOutcome.HumanReviewRequired required => required.Diagnostics,
            AdmissionOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(
                    $"conservative corpus admission failed for {source.CaseId}: {failure.Message}"),
        };
        var blocking = diagnostics
            .Where(static diagnostic =>
                diagnostic.AdmissionEffect is AdmissionEffect.Block or AdmissionEffect.HumanGate)
            .Select(static diagnostic => diagnostic.RuleId.Value)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var sl022 = diagnostics
            .Where(static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(22))
            .OrderBy(static diagnostic => diagnostic.Path, StringComparer.Ordinal)
            .ThenBy(static diagnostic => diagnostic.Message, StringComparer.Ordinal)
            .Select(static diagnostic => new ConservativeDiagnostic(
                diagnostic.RuleId.Value,
                diagnostic.Path,
                diagnostic.Message))
            .ToImmutableArray();
        return new ConservativeCaseResult(
            source.CaseId,
            source.CaseRoot,
            evaluation.Outcome is AdmissionOutcome.Admitted
                ? ConservativeDisposition.Admit
                : ConservativeDisposition.Block,
            blocking,
            sl022);
    }

    private static RepositorySnapshot Decode(
        ImmutableArray<ConservativeCorpusFile> files,
        IReadOnlyDictionary<string, ImmutableArray<byte>> objects)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(file =>
            new RawRepositoryEntry(file.Path, objects[file.ObjectRoot])));
        return SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new FormatException(failure.Message),
        };
    }

    private static Dictionary<string, LeanFileReport> Reports(
        ImmutableArray<ConservativeCorpusLeanFile> files) =>
        files.ToDictionary(
            static item => item.Path,
            static item => new LeanFileReport(
                item.Imports,
                item.Declarations.Select(static declaration => new LeanDeclaration(
                    declaration.Name,
                    declaration.Kind,
                    declaration.TypeRepresentation,
                    declaration.Axioms)
                {
                    IncludeInStatement = declaration.IncludeInStatement,
                    NameKey = declaration.NameKey,
                }).ToImmutableArray(),
                item.Error),
            StringComparer.Ordinal);

    private static void RequireStrictOrder(IEnumerable<string> values, string context)
    {
        string? previous = null;
        foreach (var value in values)
        {
            if (string.IsNullOrWhiteSpace(value)
                || previous is not null && string.CompareOrdinal(previous, value) >= 0)
            {
                throw new FormatException($"conservative corpus {context} must be sorted and unique");
            }

            previous = value;
        }
    }

    private sealed record ConservativeCorpusDocument(
        string Schema,
        ImmutableArray<ConservativeCorpusObject> Objects,
        ImmutableArray<ConservativeCorpusCase> Cases);

    private sealed record ParsedCorpus(
        ImmutableArray<ConservativeCorpusCase> Cases,
        ImmutableDictionary<string, ImmutableArray<byte>> Objects);
}
