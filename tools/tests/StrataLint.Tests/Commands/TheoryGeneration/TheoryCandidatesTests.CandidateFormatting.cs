using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed partial class TheoryCandidatesTests
{
    private static string CandidateInventory(IEnumerable<JsonElement> candidates) =>
        string.Join(
            ", ",
            candidates
                .Select(static candidate => (
                    SourceRef: candidate.GetProperty("source_ref").GetString() ?? "<null>",
                    SourceKind: candidate.GetProperty("source_kind").GetString() ?? "<null>",
                    DownstreamLane: candidate.GetProperty("downstream_lane").GetString() ?? "<null>"))
                .OrderBy(static candidate => candidate.SourceRef, StringComparer.Ordinal)
                .ThenBy(static candidate => candidate.SourceKind, StringComparer.Ordinal)
                .ThenBy(static candidate => candidate.DownstreamLane, StringComparer.Ordinal)
                .Select(static candidate =>
                    $"[source_ref={candidate.SourceRef}; source_kind={candidate.SourceKind}; "
                    + $"downstream_lane={candidate.DownstreamLane}]"));

    private static string CandidateSetSha256(JsonElement candidates)
    {
        var canonical = StructuredCanonicalWriter.WriteJson(candidates);
        var prefix = Encoding.UTF8.GetBytes("theory-candidate-set-v1\0");
        return "sha256:" + Convert.ToHexStringLower(SHA256.HashData(
            prefix.Concat(canonical).ToArray()));
    }
}
