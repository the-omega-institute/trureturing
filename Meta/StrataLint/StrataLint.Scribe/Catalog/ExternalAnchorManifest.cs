using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Scribe;

public static class ExternalAnchorManifest
{
    public const string RelativePath = "Meta/StrataLint/Golden/external-anchors.toml";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex NamePattern = new(
        "^[A-Z][A-Za-z0-9]*$",
        RegexOptions.CultureInvariant);
    private static readonly Lazy<ImmutableArray<AnchorDefinition>> Definitions = new(
        () => LoadRepository(FindRepositoryRoot()));

    public static ImmutableArray<AnchorDefinition> All => Definitions.Value;

    internal static ImmutableArray<AnchorDefinition> LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var path = Path.Combine(repositoryRoot, RelativePath);
        var bytes = File.ReadAllBytes(path);
        if (bytes.Length >= 3
            && bytes[0] == 0xEF
            && bytes[1] == 0xBB
            && bytes[2] == 0xBF
            || bytes.AsSpan().Contains((byte)'\r')
            || bytes.Length == 0
            || bytes[^1] != (byte)'\n')
        {
            throw new FormatException("External anchor data must be strict UTF-8 with LF and no BOM/CR.");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("External anchor data must be strict UTF-8.", exception);
        }

        TomlTable root;
        try
        {
            root = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw new FormatException("External anchor data decoded to null.");
        }
        catch (TomlException exception)
        {
            throw new FormatException("External anchor TOML is invalid.", exception);
        }

        if (!root.Keys.Order(StringComparer.Ordinal).SequenceEqual(["anchors", "schema_version"], StringComparer.Ordinal)
            || root["schema_version"] is not 1L
            || root["anchors"] is not TomlTableArray anchors
            || anchors.Count == 0)
        {
            throw new FormatException("External anchor root schema is invalid.");
        }

        var definitions = anchors.Select(Parse).OrderBy(
            static item => item.Anchor.CanonicalString,
            StringComparer.Ordinal).ToArray();
        if (definitions.Select(static item => item.Name).Distinct(StringComparer.Ordinal).Count() != definitions.Length
            || definitions.Select(static item => item.Anchor.CanonicalString)
                .Distinct(StringComparer.Ordinal).Count() != definitions.Length)
        {
            throw new FormatException("External anchor names and identities must be unique.");
        }

        return ImmutableArray.CreateRange(definitions);
    }

    private static AnchorDefinition Parse(TomlTable table)
    {
        if (!table.Keys.Order(StringComparer.Ordinal).SequenceEqual(
                ["anchor", "name", "provenance"],
                StringComparer.Ordinal)
            || table["name"] is not string name
            || !NamePattern.IsMatch(name)
            || table["anchor"] is not string anchor
            || table["provenance"] is not string provenance)
        {
            throw new FormatException("External anchor row schema is invalid.");
        }

        return new AnchorDefinition(name, Anchor.ParseCanonical(anchor), provenance);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, RelativePath)))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException(
            $"Could not locate repository data {RelativePath} from the Scribe assembly.");
    }
}
