using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class C0TowerProjection
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ImmutableArray<byte> Write(
        ReadOnlySpan<byte> towerBytes,
        ImmutableArray<string> members)
    {
        var parsed = TowerManifestParser.Parse(towerBytes) switch
        {
            TowerManifestParseOutcome.Loaded loaded => loaded.Syntax,
            TowerManifestParseOutcome.Invalid invalid =>
                throw new FormatException($"TOWER is invalid: {invalid.Message}"),
        };
        var component = parsed.Components.SingleOrDefault(static item =>
            item.Id == C0CeremonyProjection.ComponentId)
            ?? throw new FormatException("TOWER C0 component is missing or duplicated");
        if (component.Kind != "phased-gate")
        {
            throw new FormatException("TOWER C0 component is not a phased gate");
        }

        var text = StrictUtf8.GetString(towerBytes);
        if (text.Contains('\r') || !text.EndsWith('\n'))
        {
            throw new FormatException("TOWER must use canonical LF text with a final newline");
        }

        var componentMarker = "  - id: " + C0CeremonyProjection.ComponentId + "\n";
        var componentStart = UniqueIndexOf(text, componentMarker, "C0 component");
        var membersMarker = "    members:\n";
        var membersStart = text.IndexOf(
            membersMarker,
            componentStart + componentMarker.Length,
            StringComparison.Ordinal);
        var membersEnd = text.IndexOf(
            "    judged_by:\n",
            membersStart + membersMarker.Length,
            StringComparison.Ordinal);
        if (membersStart < 0 || membersEnd < 0)
        {
            throw new FormatException("TOWER C0 member block is not canonical");
        }

        var block = new StringBuilder(membersMarker);
        foreach (var member in members)
        {
            if (member.Contains('"') || member.Contains('\\') || member.Contains('\n'))
            {
                throw new FormatException("C0 member cannot be represented canonically in TOWER");
            }

            block.Append("      - ");
            if (member.StartsWith("c0/", StringComparison.Ordinal)) block.Append('"');
            block.Append(member);
            if (member.StartsWith("c0/", StringComparison.Ordinal)) block.Append('"');
            block.Append('\n');
        }

        var output = text[..membersStart] + block + text[membersEnd..];
        var bytes = ImmutableArray.CreateRange(StrictUtf8.GetBytes(output));
        var reparsed = TowerManifestParser.Parse(bytes.AsSpan()) switch
        {
            TowerManifestParseOutcome.Loaded loaded => loaded.Syntax,
            TowerManifestParseOutcome.Invalid invalid =>
                throw new FormatException($"generated TOWER is invalid: {invalid.Message}"),
        };
        var generated = reparsed.Components.Single(static item =>
            item.Id == C0CeremonyProjection.ComponentId);
        if (!generated.Members.SequenceEqual(members, StringComparer.Ordinal))
        {
            throw new InvalidOperationException("generated TOWER C0 members did not round-trip");
        }

        return bytes;
    }

    internal static ImmutableArray<string> ReadMembers(ReadOnlySpan<byte> towerBytes)
    {
        var parsed = TowerManifestParser.Parse(towerBytes) switch
        {
            TowerManifestParseOutcome.Loaded loaded => loaded.Syntax,
            TowerManifestParseOutcome.Invalid invalid =>
                throw new FormatException($"TOWER is invalid: {invalid.Message}"),
        };
        return parsed.Components.Single(static item =>
            item.Id == C0CeremonyProjection.ComponentId).Members;
    }

    private static int UniqueIndexOf(string text, string value, string label)
    {
        var first = text.IndexOf(value, StringComparison.Ordinal);
        if (first < 0 || text.IndexOf(value, first + value.Length, StringComparison.Ordinal) >= 0)
        {
            throw new FormatException($"TOWER {label} is missing or duplicated");
        }

        return first;
    }
}
