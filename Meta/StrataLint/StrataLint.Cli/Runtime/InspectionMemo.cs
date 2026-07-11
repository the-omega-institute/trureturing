using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Content-addressed memo for trusted Lean inspection reports. Each entry is
// keyed by (module, sha256 of the module's .olean). Lake rebuilds an .olean
// whenever the module source or anything upstream changes, so a key hit is
// exactly as trustworthy as re-running the inspector on that module. The memo
// lives under .lake/build so both the SeedBuildArtifacts snapshot copy and the
// CI actions/cache carry it for free. Any malformed memo is discarded whole:
// the failure mode is slow (full re-inspection), never wrong.
internal sealed class InspectionMemo
{
    private const int Version = 1;
    private static readonly UTF8Encoding StrictUtf8 = new(encoderShouldEmitUTF8Identifier: false, throwOnInvalidBytes: true);

    private readonly Dictionary<string, MemoEntry> entries;

    private InspectionMemo(Dictionary<string, MemoEntry> entries) => this.entries = entries;

    private sealed record MemoEntry(string OleanSha256, LeanFileReport Report);

    private static string PathFor(string root) =>
        Path.Combine(root, ".lake", "build", "stratalint-inspection-v1.json");

    public static InspectionMemo Load(string root)
    {
        var path = PathFor(root);
        if (!File.Exists(path))
        {
            return new InspectionMemo(new Dictionary<string, MemoEntry>(StringComparer.Ordinal));
        }

        try
        {
            using var document = JsonDocument.Parse(File.ReadAllBytes(path));
            var rootElement = document.RootElement;
            if (rootElement.GetProperty("version").GetInt32() != Version)
            {
                return new InspectionMemo(new Dictionary<string, MemoEntry>(StringComparer.Ordinal));
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
                            .ToImmutableArray()))
                    .ToImmutableArray();
                loaded.Add(property.Name, new MemoEntry(
                    value.GetProperty("olean_sha256").GetString() ?? throw new JsonException("missing olean hash"),
                    new LeanFileReport(imports, declarations)));
            }

            return new InspectionMemo(loaded);
        }
        catch (Exception exception) when (exception is JsonException or KeyNotFoundException or InvalidOperationException or IOException)
        {
            // Fail open to slow, never to wrong: a damaged memo is simply ignored.
            return new InspectionMemo(new Dictionary<string, MemoEntry>(StringComparer.Ordinal));
        }
    }

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
