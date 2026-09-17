using System.Collections.Immutable;
using System.Text;
using Tomlyn.Syntax;

namespace StrataLint.Engine;

// The identity covers the validated policy, including membership, custody, symlinks,
// digestion eligibility and every reserved Evidence format; comments are not authority.
internal static class FileMapCanonicalWriter
{
    internal static ImmutableArray<byte> Write(FileMapManifest manifest)
    {
        var text = new StringBuilder("schema_version = 3\n\n[residence_policy]\n");
        Field("case_id", manifest.ResidencePolicy.CaseId);
        Field("desired", manifest.ResidencePolicy.Desired);
        text.Append("known_violation_count = ").Append(manifest.ResidencePolicy.KnownViolationCount).Append('\n');
        Field("status", manifest.ResidencePolicy.Status);
        foreach (var (id, kind) in manifest.ArtifactKinds.OrderBy(static pair => pair.Key.Value, StringComparer.Ordinal))
        {
            text.Append("\n[evidence.artifact_kinds.").Append(Quote(id.Value)).Append("]\n");
            Field("profile", kind.Profile switch
            {
                ValidationProfile.StructuredJson => "structured-json",
                ValidationProfile.StructuredYaml => "structured-yaml",
                ValidationProfile.OpaqueText => "opaque-text",
                _ => throw new FormatException("unsupported FILEMAP Evidence profile"),
            });
            List("selectors", kind.Selectors);
            List("path_selectors", kind.PathSelectors);
        }
        foreach (var entry in manifest.Entries.OrderBy(static entry => entry.Pattern, StringComparer.Ordinal))
        {
            text.Append("[[files]]\n");
            Field("pattern", entry.Pattern);
            Field("kind", entry.Kind.ToString().ToLowerInvariant());
            Field("admission_plane", entry.AdmissionPlane.ToString().ToLowerInvariant());
            Field("produced_by", entry.ProducedBy);
            List("consumed_by", entry.ConsumedBy);
            List("verified_by", entry.VerifiedBy);
            Field("artifact_id", entry.ArtifactId);
            Field("runtime_disposition", entry.RuntimeDisposition);
            if (entry.Mode is not null) Field("mode", entry.Mode);
            if (entry.HistoryRequirement is not null) Field("history_requirement", entry.HistoryRequirement);
            if (entry.ResidenceViolation) text.Append("residence_violation = true\n");
            if (entry.DigestionSource) text.Append("digestion_source = true\n");
            if (entry.Symlink is { } link)
                text.Append("symlink = { target = ").Append(Quote(link.Target))
                    .Append(", kind = ").Append(Quote(link.Kind.ToString().ToLowerInvariant())).Append(" }\n");
        }
        return ImmutableArray.CreateRange(new UTF8Encoding(false, true).GetBytes(text.ToString()));

        void Field(string key, string value) => text.Append(key).Append(" = ").Append(Quote(value)).Append('\n');
        void List(string key, IEnumerable<string> values) => text.Append(key).Append(" = [")
            .AppendJoin(", ", values.Order(StringComparer.Ordinal).Select(Quote)).Append("]\n");
    }

    private static string Quote(string value) => new StringValueSyntax(value).ToString();
}
