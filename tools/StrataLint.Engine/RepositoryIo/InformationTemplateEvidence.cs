using System.Collections.Immutable;
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

internal sealed record InformationTemplateHistoricalEvidence(
    RepositorySnapshot Snapshot, LeanAxiomReport Report);

internal sealed record InformationTemplateEvidenceContext(
    string ProtectedRevision,
    Func<string, InformationTemplateHistoricalEvidence> ReadHistorical);

internal static class InformationTemplateEvidence
{
    // The historical content is data evaluated by today's producer. Keep its
    // D5 sources and state; bind configuration/toolchain inputs to the current program.
    internal static RepositorySnapshot HistoricalInputs(RepositorySnapshot historical, RepositorySnapshot current)
    {
        static bool ProducerInput(string path) => path.StartsWith("tools/lean-inspector/", StringComparison.Ordinal)
            || path is "Meta/lean-report.toml" or "lean-report-inputs.json" or "lean-toolchain" or "lake-manifest.json" or "lakefile.toml";
        var files = historical.Files.RemoveRange(historical.Files.Keys.Where(path => ProducerInput(path.Value)))
            .SetItems(current.Files.Where(pair => ProducerInput(pair.Key.Value)));
        return RepositorySnapshot.Create(files);
    }

    internal static InformationTemplateModuleEvidence Read(
        JsonElement value, string sourcePath, RepositorySnapshot snapshot)
    {
        InformationTemplateJson.Fields(value, "schema_version", "compatibility_version", "inventory",
            "records", "registered", "inputs");
        InformationTemplateJson.Version(value);
        if (value.GetProperty("compatibility_version").GetRawText() != "5")
            throw new FormatException("DTR-Evidence: old report is not current binding evidence");
        var inputs = InformationTemplateDebtStore.ReadInputs(value.GetProperty("inputs"), snapshot);
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
                "unit_name", "realization_name");
            var key = InformationTemplateDebtStore.ReadKey(record.GetProperty("key"));
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
            var contentInputs = InformationTemplateDebtStore.ReadInputs(record.GetProperty("content_inputs"), snapshot);
            if (!contentInputs.Any(input => input.Path == registration)
                || contentInputs.Any(input => !inputs.Contains(input)))
                throw new FormatException("DTR-Evidence: registration/content source not in current input closure");
            var binding = OptionalString(record, "binding_source_path");
            var diagnostic = OptionalString(record, "diagnostic");
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
                if (InformationTemplateDebtStore.ReadKey(certificate.GetProperty("key")) != key
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
            records.Add(new(key, registration, statement, contentInputs, state, reference, diagnostic, binding, unit, realization));
        }
        return new(value.Clone(), inventory, records.ToImmutable(), registered, inputs);
    }

    private static string MissingDeclarationDiagnostic(InformationOccurrenceKey key) =>
        $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}";

    // The inspector library has its own Lean source root in lakefile.toml.
    // This also permits its real command fixtures to cross the same wire reader.
    internal static string ModuleForSource(string path)
    {
        const string inspectorRoot = "tools/lean-inspector/";
        var relative = path.StartsWith(inspectorRoot, StringComparison.Ordinal)
            ? path[inspectorRoot.Length..] : path;
        return LeanImportClosure.ModuleName(RepoPath.CreateKnown(relative));
    }

    // Binding compatibility is the manual report_semantic_version tag, not
    // an Inspector source fingerprint. These are configuration/toolchain inputs.
    private static readonly string[] PolicyInputs = [
        "lean-report-inputs.json", "lean-toolchain", "lake-manifest.json"];

    internal static InformationTemplateUniverse Collect(RepositorySnapshot snapshot, LeanAxiomReport report)
    {
        var governed = snapshot.Files.Keys.Where(path => path.Value.StartsWith("D5/", StringComparison.Ordinal)
                && path.Value.EndsWith(".lean", StringComparison.Ordinal))
            .Select(path => path.Value).ToImmutableHashSet(StringComparer.Ordinal);
        var assessed = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var inventory = ImmutableHashSet.CreateBuilder<InformationOccurrenceKey>();
        var registered = ImmutableHashSet.CreateBuilder<InformationOccurrenceKey>();
        var claims = new Dictionary<InformationOccurrenceKey, List<InformationTemplateOccurrence>>();
        foreach (var source in governed.Order(StringComparer.Ordinal))
        {
            if (!report.Files.TryGetValue(RepoPath.CreateKnown(source), out var module) || module.Error is not null
                || module.InformationTemplates is not { } evidence)
                throw new FormatException($"DTR-Evidence: missing current producer for {source}");
            var requiredInputs = LeanImportClosure.RepositoryPaths(report, RepoPath.CreateKnown(source))
                .Select(path => path.Value).Concat(PolicyInputs).ToHashSet(StringComparer.Ordinal);
            foreach (var required in requiredInputs.Order(StringComparer.Ordinal))
                if (!evidence.Inputs.Any(input => input.Path == required))
                    throw new FormatException("DTR-Evidence: omitted required producer/source input " + required);
            assessed.Add(source);
            foreach (var key in evidence.Inventory)
                if (!inventory.Add(key)) throw new FormatException("DTR-Inventory: duplicate occurrence owner");
            foreach (var key in evidence.Registered)
                if (!registered.Add(key)) throw new FormatException("DTR-Inventory: duplicate retained registration");
            foreach (var occurrence in evidence.Records)
            {
                if (!claims.TryGetValue(occurrence.Key, out var list)) claims.Add(occurrence.Key, list = []);
                list.Add(occurrence);
            }
        }
        if (!inventory.SetEquals(registered) || !inventory.SetEquals(claims.Keys))
            throw new FormatException("DTR-Inventory: command inventory, retained units and binding records differ");
        var joined = ImmutableDictionary.CreateBuilder<InformationOccurrenceKey, InformationTemplateOccurrence>();
        foreach (var (key, records) in claims)
        {
            var originals = records.Where(record => record.BindingSourcePath is null
                || record.BindingSourcePath == record.RegistrationSourcePath).ToArray();
            if (originals.Length != 1) throw new FormatException("DTR-Inventory: original registration owner missing/duplicate");
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
                throw new FormatException("DTR-Inventory: retained unit/realization owner is missing or ambiguous");
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
        return new(joined.ToImmutable(), inventory.ToImmutable(), governed, assessed.ToImmutable());
    }

    private static IEnumerable<JsonElement> Array(JsonElement value, string name)
    {
        if (value.GetProperty(name).ValueKind != JsonValueKind.Array)
            throw new FormatException("DTR-Evidence: array required: " + name);
        return value.GetProperty(name).EnumerateArray();
    }

    private static ImmutableHashSet<InformationOccurrenceKey> ReadKeys(JsonElement array)
    {
        if (array.ValueKind != JsonValueKind.Array) throw new FormatException("DTR-Inventory: key array required");
        var keys = ImmutableHashSet.CreateBuilder<InformationOccurrenceKey>();
        foreach (var item in array.EnumerateArray())
            if (!keys.Add(InformationTemplateDebtStore.ReadKey(item)))
                throw new FormatException("DTR-Inventory: duplicate key");
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
