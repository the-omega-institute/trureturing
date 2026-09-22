using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    // General rule fixtures have no information registrations. Supply the same
    // empty wire inventory as the current producer; explicit evidence is retained.
    private Dictionary<string, LeanFileReport> ReportsWithEmptyTemplateEvidence(RepositorySnapshot snapshot)
    {
        var wire = JsonSerializer.SerializeToElement(new
        {
            schema_version = 1,
            compatibility_version = DeclaredTemplateReviewTests.ManifestVersion(DeclaredTemplateReviewTests.PolicyFiles()),
            inventory = Array.Empty<object>(), registered = Array.Empty<object>(), records = Array.Empty<object>(),
        });
        return Reports.ToDictionary(pair => pair.Key, pair => pair.Value.InformationTemplates is not null ? pair.Value
            : pair.Value with { InformationTemplates = wire }, StringComparer.Ordinal);
    }
}
