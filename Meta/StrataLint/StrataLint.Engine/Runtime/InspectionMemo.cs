using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

// Content-addressed memo for trusted Lean inspection reports. Each entry is
// keyed by (harness report format, module, sha256 of the module's .olean).
// The report format binds the inspector encoder and statement-id encoding, so
// either harness change discards the memo whole. The failure mode is always
// slow (full re-inspection), never wrong.
internal sealed class InspectionMemo
{
    private const int Version = 1;

    private readonly string harnessFormatVersion;
    private readonly Dictionary<string, MemoEntry> entries;

    private InspectionMemo(string harnessFormatVersion, Dictionary<string, MemoEntry> entries)
    {
        this.harnessFormatVersion = harnessFormatVersion;
        this.entries = entries;
    }

    private sealed record MemoEntry(string OleanSha256, LeanFileReport Report);

    private static string PathFor(string root) =>
        Path.Combine(root, ".lake", "build", "stratalint-inspection-v1.json");

    public static InspectionMemo Load(string root, string harnessFormatVersion)
    {
        var path = PathFor(root);
        if (!File.Exists(path))
        {
            return Empty(harnessFormatVersion);
        }

        try
        {
            using var document = JsonDocument.Parse(File.ReadAllBytes(path));
            var rootElement = document.RootElement;
            if (rootElement.GetProperty("version").GetInt32() != Version
                || !string.Equals(
                    rootElement.GetProperty("harness_format_version").GetString(),
                    harnessFormatVersion,
                    StringComparison.Ordinal))
            {
                return Empty(harnessFormatVersion);
            }

            var loaded = new Dictionary<string, MemoEntry>(StringComparer.Ordinal);
            foreach (var property in rootElement.GetProperty("entries").EnumerateObject())
            {
                var value = property.Value;
                var imports = value.GetProperty("imports")
                    .EnumerateArray()
                    .Select(static item => item.GetString() ?? throw new JsonException("non-string import"))
                    .ToImmutableArray();
                var declarations = value.GetProperty("declarations")
                    .EnumerateArray()
                    .Select(static item => new LeanDeclaration(
                        item.GetProperty("name").GetString() ?? throw new JsonException("missing name"),
                        item.GetProperty("kind").GetString() ?? throw new JsonException("missing kind"),
                        item.GetProperty("type").GetString() ?? throw new JsonException("missing type"),
                        item.GetProperty("axioms")
                            .EnumerateArray()
                            .Select(static axiom => axiom.GetString() ?? throw new JsonException("non-string axiom"))
                            .ToImmutableArray())
                    {
                        NameKey = item.GetProperty("name_key").GetString()
                            ?? throw new JsonException("missing name key"),
                        IncludeInStatement = item.GetProperty("include_in_statement").GetBoolean(),
                    })
                    .ToImmutableArray();
                loaded.Add(property.Name, new MemoEntry(
                    value.GetProperty("olean_sha256").GetString() ?? throw new JsonException("missing olean hash"),
                    new LeanFileReport(imports, declarations)));
            }

            return new InspectionMemo(harnessFormatVersion, loaded);
        }
        catch (Exception exception) when (exception is JsonException or KeyNotFoundException or InvalidOperationException or IOException)
        {
            // Fail open to slow, never to wrong: a damaged memo is simply ignored.
            return Empty(harnessFormatVersion);
        }
    }

    private static InspectionMemo Empty(string harnessFormatVersion) =>
        new(harnessFormatVersion, new Dictionary<string, MemoEntry>(StringComparer.Ordinal));

    public bool TryGet(string module, string oleanSha256, out LeanFileReport report)
    {
        if (entries.TryGetValue(module, out var entry)
            && string.Equals(entry.OleanSha256, oleanSha256, StringComparison.Ordinal))
        {
            report = entry.Report;
            return true;
        }

        report = null!;
        return false;
    }

    public void Put(string module, string oleanSha256, LeanFileReport report) =>
        entries[module] = new MemoEntry(oleanSha256, report);

    public void Save(string root)
    {
        var path = PathFor(root);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        using var stream = new MemoryStream();
        using (var writer = new Utf8JsonWriter(stream, new JsonWriterOptions { Indented = false }))
        {
            writer.WriteStartObject();
            writer.WriteNumber("version", Version);
            writer.WriteString("harness_format_version", harnessFormatVersion);
            writer.WriteStartObject("entries");
            foreach (var pair in entries.OrderBy(static pair => pair.Key, StringComparer.Ordinal))
            {
                writer.WriteStartObject(pair.Key);
                writer.WriteString("olean_sha256", pair.Value.OleanSha256);
                writer.WriteStartArray("imports");
                foreach (var import in pair.Value.Report.Imports) writer.WriteStringValue(import);
                writer.WriteEndArray();
                writer.WriteStartArray("declarations");
                foreach (var declaration in pair.Value.Report.Declarations)
                {
                    writer.WriteStartObject();
                    writer.WriteString("name", declaration.Name);
                    writer.WriteString("name_key", declaration.NameKey);
                    writer.WriteBoolean("include_in_statement", declaration.IncludeInStatement);
                    writer.WriteString("kind", declaration.Kind);
                    writer.WriteString("type", declaration.TypeRepresentation);
                    writer.WriteStartArray("axioms");
                    foreach (var axiom in declaration.Axioms) writer.WriteStringValue(axiom);
                    writer.WriteEndArray();
                    writer.WriteEndObject();
                }

                writer.WriteEndArray();
                writer.WriteEndObject();
            }

            writer.WriteEndObject();
            writer.WriteEndObject();
        }

        File.WriteAllBytes(path, stream.ToArray());
    }
}
