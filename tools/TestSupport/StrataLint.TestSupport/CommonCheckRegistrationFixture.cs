using System.Text.Json;

namespace StrataLint.TestSupport;

public static class CommonCheckRegistrationFixture
{
    public static string[] Ids => ["SL-001", "SL-002", "SL-003", "SL-004", "SL-006", "SL-008", "SL-010", "SL-011", "SL-012", "SL-015", "SL-017", "SL-018", "SL-019", "SL-020", "SL-021", "SL-023", "SL-025", "SL-026", "selftest-pair", "capability-proof", "banned-api-proof", "scribe-projections", "scribe-describe", "scribe-markdown", "filemap"];
    public static string Manifest(string project) => JsonSerializer.Serialize(new
    {
        schema = "ci-check-input-registration-v1",
        checks = Ids.Select(id => new { id, program_projects = new[] { project }, materials = Array.Empty<string>(),
            material_excludes = Array.Empty<string>(), path_inventory = Array.Empty<string>(), report_inputs = Array.Empty<object>() }),
    });
    public const string ScribeMaterial = "{\"Version\":1,\"Records\":[],\"References\":[],\"Latex\":[]}";
    public static string Predicate(string id) => "{\"rule\":\"" + id + "\",\"diagnostics\":[]}";
}
