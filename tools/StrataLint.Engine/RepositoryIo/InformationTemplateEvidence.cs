using System.Collections.Immutable;
using System.Collections.Concurrent;
using System.Runtime.CompilerServices;
using System.Text.Json;

namespace StrataLint.Engine;

// Current-compiler evidence is source-bound independently for each module. Null
// is an old/missing producer, never an empty inventory.
internal sealed record InformationTemplateModuleEvidence(
    JsonElement Wire,
    ImmutableHashSet<InformationOccurrenceKey> Inventory,
    ImmutableArray<InformationTemplateOccurrence> Records,
    ImmutableHashSet<InformationOccurrenceKey> Registered,
    ImmutableArray<InformationTemplateContentInput> Inputs);

internal static class InformationTemplateEvidence
{
    // RepositorySnapshot and its files are immutable. Share only their parsed
    // link policy and byte digests; every wire record is still checked below.
    // A replacement snapshot gets an independent index, even for equal paths.
    private static readonly ConditionalWeakTable<RepositorySnapshot, InputIndex> InputIndices = new();

    private sealed class InputIndex(RepositorySnapshot snapshot)
    {
        private readonly ImmutableArray<FileMapSymlink> links =
            snapshot.TryGetFile(AdmissionPlanePolicy.FileMapPath, out var manifest)
                ? FileMapSymlinkPolicy.Parse(manifest.RawBytes.AsSpan(), AdmissionPlanePolicy.FileMapPath,
                    path => snapshot.TryGetFile(path, out var included)
                        ? included.RawBytes.ToArray()
                        : throw new KeyNotFoundException(path))
                : [];
        private readonly ConcurrentDictionary<string, string> hashes = new(StringComparer.Ordinal);

        internal bool Matches(string path, string digest) =>
            !links.Any(link => path == link.Path || path.StartsWith(link.Path + "/", StringComparison.Ordinal))
            && snapshot.TryGetFile(path, out var file)
            && hashes.GetOrAdd(path, _ => InformationTemplateJson.Sha256(file.RawBytes.AsSpan())) == digest;
    }

    private static ImmutableArray<InformationTemplateContentInput> ReadInputs(JsonElement value, RepositorySnapshot inputs)
    {
        if (value.ValueKind != JsonValueKind.Array || value.GetArrayLength() == 0)
            throw new FormatException("DTR-Evidence: nonempty content inputs required");
        var result = ImmutableArray.CreateBuilder<InformationTemplateContentInput>();
        var index = InputIndices.GetValue(inputs, static snapshot => new InputIndex(snapshot));
        string? previous = null;
        foreach (var item in value.EnumerateArray())
        {
            InformationTemplateJson.Fields(item, "path", "sha256");
            var path = InformationTemplateJson.String(item, "path");
            var sha256 = InformationTemplateJson.Hash(InformationTemplateJson.String(item, "sha256"), 64);
            if (!RepoPath.TryCreate(path, out _) || path.Contains('\\')
                || path.Split('/').Any(part => part is "" or "." or "..")
                || previous is not null && string.CompareOrdinal(previous, path) >= 0
                || !index.Matches(path, sha256))
                throw new FormatException($"DTR-Evidence: unavailable, changed or noncanonical input {path}");
            previous = path;
            result.Add(new(path, sha256));
        }

        return result.ToImmutable();
    }

    private static string ManifestVersion(RepositorySnapshot snapshot)
    {
        const string error = "DTR-ManifestVersion: lean-report-inputs.json requires a positive integer report_semantic_version";
        if (!snapshot.Files.TryGetValue(RepoPath.CreateKnown("lean-report-inputs.json"), out var manifest))
            throw new FormatException(error);
        try
        {
            using var document = JsonDocument.Parse(manifest.RawBytes.AsMemory());
            var root = document.RootElement;
            if (root.ValueKind != JsonValueKind.Object
                || root.EnumerateObject().Count(p => p.Name == "report_semantic_version") != 1
                || !root.TryGetProperty("report_semantic_version", out var value)
                || value.ValueKind != JsonValueKind.Number)
                throw new FormatException(error);
            var version = value.GetRawText();
            if (version.Length == 0 || version[0] is < '1' or > '9'
                || version.Any(c => c is < '0' or > '9'))
                throw new FormatException(error);
            return version;
        }
        catch (JsonException ex)
        {
            throw new FormatException(error, ex);
        }
    }

    internal static InformationTemplateModuleEvidence Read(
        JsonElement value, string sourcePath, RepositorySnapshot snapshot)
    {
        if (value.ValueKind == JsonValueKind.Object
            && (!value.TryGetProperty("compatibility_version", out var compatibility)
                || compatibility.ValueKind != JsonValueKind.Number))
            throw new FormatException("DTR-EvidenceVersion: compatibility_version requires a positive integer");
        InformationTemplateJson.Fields(value, "schema_version", "compatibility_version", "inventory",
            "records", "registered", "inputs");
        InformationTemplateJson.Version(value);
        if (value.GetProperty("compatibility_version").GetRawText() != ManifestVersion(snapshot))
            throw new FormatException("DTR-EvidenceVersion: compatibility_version differs from report_semantic_version");
        var inputs = ReadInputs(value.GetProperty("inputs"), snapshot);
        if (!inputs.Any(input => input.Path == sourcePath))
            throw new FormatException("DTR-Evidence: producer source is not bound");
        var inventory = ReadKeys(value.GetProperty("inventory"));
        var registered = ReadKeys(value.GetProperty("registered"));
        var records = ImmutableArray.CreateBuilder<InformationTemplateOccurrence>();
        var keys = new HashSet<InformationOccurrenceKey>();
        foreach (var record in Array(value, "records"))
        {
            InformationTemplateJson.Fields(record, "key", "registration_source_path", "statement_identity",
                "content_inputs", "binding_source_path", "state", "diagnostic", "certificate",
                "unit_name", "realization_name", "escape_from", "escape_continues", "bridge_kind");
            var key = InformationTemplateJson.ReadKey(record.GetProperty("key"));
            if (!keys.Add(key)) throw new FormatException("DTR-Evidence: duplicate binding record");
            var registration = InformationTemplateJson.String(record, "registration_source_path");
            // Generated names are compiler display spellings, not source-level
            // identifiers: a component containing » cannot be escaped by
            // Name.toString. Collect resolves each spelling to exactly one
            // source-bound declaration; occurrence keys keep the strict parser.
            var unit = InformationTemplateJson.String(record, "unit_name");
            var realization = InformationTemplateJson.String(record, "realization_name");
            if (key.RegistrationModule != ModuleForSource(registration))
                throw new FormatException("DTR-Evidence: registration module/source owner differs");
            var statement = InformationTemplateJson.Hash(InformationTemplateJson.String(record, "statement_identity"), 64);
            var contentInputs = ReadInputs(record.GetProperty("content_inputs"), snapshot);
            if (!contentInputs.Any(input => input.Path == registration)
                || contentInputs.Any(input => !inputs.Contains(input)))
                throw new FormatException("DTR-Evidence: registration/content source not in current input closure");
            var binding = OptionalString(record, "binding_source_path");
            var diagnostic = OptionalString(record, "diagnostic");
            var escapeFrom = ReadEscapeFrom(record.GetProperty("escape_from"));
            var escapeContinues = ReadEscapeContinues(record.GetProperty("escape_continues"));
            var bridgeKind = InformationTemplateJson.String(record, "bridge_kind");
            if (bridgeKind is not ("legacy" or "forward"))
                throw new FormatException("DTR-Evidence: unknown bridge_kind");
            var certificate = record.GetProperty("certificate");
            var state = InformationTemplateJson.String(record, "state") switch
            {
                "undeclared" => InformationTemplateBindingState.Undeclared,
                "declared_unresolved" => InformationTemplateBindingState.DeclaredUnresolved,
                "declared_validated" => InformationTemplateBindingState.DeclaredValidated,
                _ => throw new FormatException("DTR-Evidence: unknown binding result"),
            };
            string? reference = null;
            if (state == InformationTemplateBindingState.DeclaredValidated)
            {
                InformationTemplateJson.Fields(certificate, "key", "evidence_ref", "plan_identity",
                    "descriptor_identity", "actual_identity", "argument_inputs", "extraction_inputs");
                if (InformationTemplateJson.ReadKey(certificate.GetProperty("key")) != key
                    || diagnostic is not null)
                    throw new FormatException("DTR-Evidence: copied certificate or contradictory result");
                reference = HashField(certificate, "evidence_ref");
                HashField(certificate, "plan_identity");
                HashField(certificate, "descriptor_identity");
                HashField(certificate, "actual_identity");
                CheckDependencies(certificate, "argument_inputs");
                CheckDependencies(certificate, "extraction_inputs");
            }
            else if (certificate.ValueKind != JsonValueKind.Null)
                throw new FormatException("DTR-Evidence: unresolved/undeclared cannot carry a certificate");
            if (state == InformationTemplateBindingState.Undeclared)
            {
                if (binding is not null || diagnostic != MissingDeclarationDiagnostic(key))
                    throw new FormatException("DTR-Evidence: undeclared declaration/diagnostic mismatch");
                if (sourcePath != registration)
                    throw new FormatException("DTR-Evidence: undeclared record has wrong producer owner");
            }
            else
            {
                if (binding != sourcePath || !inputs.Any(input => input.Path == binding)
                    || state == InformationTemplateBindingState.DeclaredUnresolved && diagnostic is null)
                    throw new FormatException("DTR-Evidence: binding owner/diagnostic is missing or wrong");
            }
            records.Add(new(key, registration, statement, contentInputs, state, reference, diagnostic, binding, unit, realization,
                escapeFrom, escapeContinues, bridgeKind));
        }
        return new(value.Clone(), inventory, records.ToImmutable(), registered, inputs);
    }

    private static InformationEscapeFrom? ReadEscapeFrom(JsonElement value)
    {
        if (value.ValueKind == JsonValueKind.Null) return null;
        InformationTemplateJson.Fields(value, "name", "type_identity", "object_identity");
        return new(InformationTemplateJson.Name(InformationTemplateJson.String(value, "name")),
            HashField(value, "type_identity"), HashField(value, "object_identity"));
    }

    private static InformationEscapeContinuation? ReadEscapeContinues(JsonElement value)
    {
        if (value.ValueKind == JsonValueKind.Null) return null;
        InformationTemplateJson.Fields(value, "kind", "declaration_name", "statement_identity", "chain_name");
        var kind = InformationTemplateJson.String(value, "kind");
        var declaration = OptionalString(value, "declaration_name");
        var statement = OptionalString(value, "statement_identity");
        var chain = OptionalString(value, "chain_name");
        if (kind == "open")
        {
            if (declaration is not null || statement is not null || chain is not null)
                throw new FormatException("DTR-Evidence: open residual cannot carry a certificate");
        }
        else if (kind is "witness" or "empty" && declaration is not null && statement is not null && chain is not null)
        {
            InformationTemplateJson.Name(declaration);
            InformationTemplateJson.Hash(statement, 64);
            InformationTemplateJson.Name(chain);
        }
        else throw new FormatException("DTR-Evidence: invalid residual certificate");
        return new(kind, declaration, statement, chain);
    }

    private static string MissingDeclarationDiagnostic(InformationOccurrenceKey key) =>
        $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}";

    internal static string ModuleForSource(string path) =>
        LeanImportClosure.ModuleName(RepoPath.CreateKnown(path));

    // Binding compatibility is the manual report_semantic_version tag, not
    // an Inspector source fingerprint. These are configuration/toolchain inputs.
    private static readonly string[] PolicyInputs = [
        "lean-report-inputs.json", "lean-toolchain", "lake-manifest.json"];

    internal static InformationTemplateUniverse Collect(RepositorySnapshot snapshot, LeanAxiomReport report,
        IEnumerable<RepoPath> sources, ImmutableHashSet<string>? theorems = null)
    {
        var governed = sources.Select(path => path.Value).ToImmutableHashSet(StringComparer.Ordinal);
        var selection = new InformationTemplateSelection(governed, theorems);
        var inventory = ImmutableHashSet.CreateBuilder<InformationOccurrenceKey>();
        var registered = ImmutableHashSet.CreateBuilder<InformationOccurrenceKey>();
        var claims = new Dictionary<InformationOccurrenceKey, List<InformationTemplateOccurrence>>();
        foreach (var source in governed.Order(StringComparer.Ordinal))
        {
            if (!report.Files.TryGetValue(RepoPath.CreateKnown(source), out var module) || module.Error is not null
                || module.InformationTemplates is not { } payload)
                throw new FormatException($"DTR-Evidence: missing current producer for {source}");
            var evidence = Read(selection.Project(payload, source), source, snapshot);
            // Match Registry.moduleSourceInputs/isRecordedModule: traversal can
            // cross tooling, but theorem evidence records content and the real
            // command fixtures. Inspector implementation identity belongs to
            // report production, not each theorem's source-input contract.
            var requiredInputs = LeanImportClosure.RepositoryPaths(report, RepoPath.CreateKnown(source))
                .Where(path => path.Value.StartsWith("D5/", StringComparison.Ordinal)
                    || path.Value == "Trureturing.lean"
                    || ModuleForSource(path.Value).StartsWith("LeanInformationAudit.Tests.", StringComparison.Ordinal))
                .Select(path => path.Value).Concat(PolicyInputs).ToHashSet(StringComparer.Ordinal);
            foreach (var required in requiredInputs.Order(StringComparer.Ordinal))
                if (!evidence.Inputs.Any(input => input.Path == required))
                    throw new FormatException("DTR-Evidence: omitted required producer/source input " + required);
            foreach (var key in evidence.Inventory)
                if (!inventory.Add(key)) throw new FormatException("DTR-Evidence: duplicate occurrence owner");
            foreach (var key in evidence.Registered)
                if (!registered.Add(key)) throw new FormatException("DTR-Evidence: duplicate retained registration");
            foreach (var occurrence in evidence.Records.Where(record => governed.Contains(record.RegistrationSourcePath)))
            {
                if (!claims.TryGetValue(occurrence.Key, out var list)) claims.Add(occurrence.Key, list = []);
                list.Add(occurrence);
            }
        }
        foreach (var (path, module) in report.Files)
        {
            if (governed.Contains(path.Value) || module.InformationTemplates is not { } payload
                || !selection.HasRecords(payload)) continue;
            if (module.Error is not null) throw new FormatException("DTR-Evidence: invalid binding producer " + path.Value);
            foreach (var occurrence in Read(selection.Project(payload, path.Value), path.Value, snapshot).Records
                .Where(record => governed.Contains(record.RegistrationSourcePath)))
            {
                if (!claims.TryGetValue(occurrence.Key, out var list)) claims.Add(occurrence.Key, list = []);
                list.Add(occurrence);
            }
        }
        if (!inventory.SetEquals(registered) || !inventory.SetEquals(claims.Keys))
            throw new FormatException("DTR-Evidence: command inventory, retained units and binding records differ");
        var joined = ImmutableDictionary.CreateBuilder<InformationOccurrenceKey, InformationTemplateOccurrence>();
        foreach (var (key, records) in claims)
        {
            var originals = records.Where(record => record.BindingSourcePath is null
                || record.BindingSourcePath == record.RegistrationSourcePath).ToArray();
            if (originals.Length != 1) throw new FormatException("DTR-Evidence: original registration owner missing/duplicate");
            var original = originals[0];
            var ownerReport = report.Files[RepoPath.CreateKnown(original.RegistrationSourcePath)];
            var realizationOwners = LeanImportClosure.RepositoryPaths(report,
                RepoPath.CreateKnown(original.RegistrationSourcePath));
            if (original.UnitName is null || original.RealizationName is null
                || ownerReport.Declarations.Count(declaration => declaration.Name == original.UnitName) != 1
                || !ownerReport.Declarations.Any(declaration => declaration.Name == original.UnitName
                    && declaration.Kind == "def")
                || realizationOwners.Sum(path => report.Files[path].Declarations.Count(
                    declaration => declaration.Name == original.RealizationName)) != 1)
                throw new FormatException("DTR-Evidence: retained unit/realization owner is missing or ambiguous");
            var declared = records.Where(record => record.State != InformationTemplateBindingState.Undeclared).ToArray();
            if (declared.Length > 1) throw new FormatException("DTR-Evidence: duplicate/contradictory inline or sidecar claim");
            var selected = declared.SingleOrDefault() ?? original;
            if (selected.StatementIdentity != original.StatementIdentity
                || selected.RegistrationSourcePath != original.RegistrationSourcePath
                || selected.UnitName != original.UnitName || selected.RealizationName != original.RealizationName)
                throw new FormatException("DTR-Evidence: sidecar retargets the occurrence");
            joined.Add(key, selected);
        }
        // Inventory is the exact join of compiler registration keys, command
        // events and records above. Seal-generated unit abbreviations are
        // declarations, not registrations; their suffix carries no authority.
        return new(joined.ToImmutable(), inventory.ToImmutable());
    }

    private static IEnumerable<JsonElement> Array(JsonElement value, string name)
    {
        if (value.GetProperty(name).ValueKind != JsonValueKind.Array)
            throw new FormatException("DTR-Evidence: array required: " + name);
        return value.GetProperty(name).EnumerateArray();
    }

    private static ImmutableHashSet<InformationOccurrenceKey> ReadKeys(JsonElement array)
    {
        if (array.ValueKind != JsonValueKind.Array) throw new FormatException("DTR-Evidence: key array required");
        var keys = ImmutableHashSet.CreateBuilder<InformationOccurrenceKey>();
        foreach (var item in array.EnumerateArray())
            if (!keys.Add(InformationTemplateJson.ReadKey(item)))
                throw new FormatException("DTR-Evidence: duplicate key");
        return keys.ToImmutable();
    }

    private static string? OptionalString(JsonElement value, string field) =>
        value.GetProperty(field).ValueKind == JsonValueKind.Null ? null : InformationTemplateJson.String(value, field);

    private static string HashField(JsonElement value, string field) =>
        InformationTemplateJson.Hash(InformationTemplateJson.String(value, field), 64);

    private static void CheckDependencies(JsonElement value, string field)
    {
        var names = new HashSet<string>(StringComparer.Ordinal);
        foreach (var input in Array(value, field))
        {
            InformationTemplateJson.Fields(input, "name", "owner", "type_identity", "body_identity");
            var name = InformationTemplateJson.Name(InformationTemplateJson.String(input, "name"));
            InformationTemplateJson.Name(InformationTemplateJson.String(input, "owner"));
            HashField(input, "type_identity");
            // Kernel primitives have no executable body.
            var body = input.GetProperty("body_identity");
            if (body.ValueKind != JsonValueKind.String) throw new FormatException("DTR-Evidence: body identity required");
            if (body.GetString() is { Length: > 0 } text) InformationTemplateJson.Hash(text, 64);
            if (!names.Add(name)) throw new FormatException("DTR-Evidence: duplicate dependency");
        }
    }
}
