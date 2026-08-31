using System.Collections.Immutable;
using System.Text.Json;
using System.Text.RegularExpressions;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal static class TailAuthorizationArtifact
{
    private const string Schema = "digestion-tail-authorization-v1";

    private static readonly Regex AtomIdPattern = new(
        "^[0-9a-f]{64}$",
        RegexOptions.CultureInvariant);

    private static readonly ImmutableHashSet<string> Fields =
        ImmutableHashSet.Create(StringComparer.Ordinal, "atom_id", "schema", "tail_gids");

    internal static string PathFor(string atomId) =>
        $"tools/Authorizations/digestion-tail/{atomId}.json";

    internal static ImmutableArray<byte> Write(string atomId, IEnumerable<string> tailGids)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(atomId);
        ArgumentNullException.ThrowIfNull(tailGids);
        if (!AtomIdPattern.IsMatch(atomId))
        {
            throw new FormatException($"invalid tail authorization atom_id {atomId}");
        }

        var gids = tailGids.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        if (gids.Length == 0 || gids.Any(static gid => !Gid.TryParse(gid, out _)))
        {
            throw new FormatException("tail authorization requires canonical target GIDs");
        }

        return StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            schema = Schema,
            atom_id = atomId,
            tail_gids = gids,
        }));
    }

    internal static bool Verify(
        DigestionLedgerEntry entry,
        IReadOnlyCollection<string> tailGids,
        RepositorySnapshot snapshot,
        bool validateStoredArtifact)
    {
        var receipt = entry.Receipts.TailAuthorization;
        if (receipt is null
            || receipt.Path != PathFor(entry.AtomId)
            || !snapshot.TryGetFile(receipt.Path, out var authorization)
            || validateStoredArtifact
                && (!DigestionFingerprint.IsCanonicalSha256(receipt.Sha256)
                    || receipt.Sha256
                        != DigestionFingerprint.Compute(authorization.RawBytes.AsSpan()).RawSha256))
        {
            return false;
        }

        try
        {
            using var document = JsonDocument.Parse(authorization.Text);
            var root = document.RootElement;
            if (root.ValueKind != JsonValueKind.Object
                || validateStoredArtifact
                    && !StructuredCanonicalWriter.WriteJson(root).AsSpan()
                        .SequenceEqual(authorization.RawBytes.AsSpan()))
            {
                return false;
            }

            var names = root.EnumerateObject().Select(static property => property.Name).ToArray();
            if (names.Length != Fields.Count
                || names.Distinct(StringComparer.Ordinal).Count() != names.Length
                || names.Any(name => !Fields.Contains(name))
                || root.GetProperty("schema").GetString() != Schema
                || root.GetProperty("atom_id").GetString() != entry.AtomId)
            {
                return false;
            }

            var gidsElement = root.GetProperty("tail_gids");
            if (gidsElement.ValueKind != JsonValueKind.Array
                || gidsElement.EnumerateArray().Any(static item => item.ValueKind != JsonValueKind.String))
            {
                return false;
            }

            var authorized = gidsElement.EnumerateArray().Select(static item => item.GetString()!).ToArray();
            var expected = tailGids.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
            return authorized.SequenceEqual(expected, StringComparer.Ordinal);
        }
        catch (Exception exception) when (exception is JsonException or InvalidOperationException)
        {
            return false;
        }
    }
}
