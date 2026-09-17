using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using Tomlyn;
using Tomlyn.Model;
using Tomlyn.Parsing;

namespace StrataLint.Engine;

internal sealed record FileMapDocument(string Path, ImmutableArray<byte> Bytes, TomlTable Table);

// Includes are explicit sibling files, never filesystem discovery. Callers supply bytes
// from the same working tree or immutable snapshot as the root manifest.
internal static class FileMapDocuments
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex FragmentName = new(
        @"\AFILEMAP(?:\.[a-z][a-z0-9]*)+\.toml\z",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

    internal static bool IsPolicyPath(string path) =>
        path == AdmissionPlanePolicy.FileMapPath
        || path.StartsWith("Meta/", StringComparison.Ordinal) && FragmentName.IsMatch(path[5..]);

    internal static ImmutableArray<FileMapDocument> Resolve(
        ReadOnlySpan<byte> bytes,
        string location,
        Func<string, byte[]>? readInclude = null)
    {
        var root = Decode(bytes, location);
        var documents = ImmutableArray.CreateBuilder<FileMapDocument>();
        documents.Add(root);
        if (!root.Table.TryGetValue("include", out var rawInclude)) return documents.ToImmutable();
        if (rawInclude is not TomlArray includes || includes.Count == 0
            || includes.Any(item => item is not string name || !FragmentName.IsMatch(name)))
            throw new FileMapParseException(location,
                "include must be a nonempty array of FILEMAP.<scope>.toml names; scope segments use lowercase letters and digits, separated by dots");

        var names = includes.Cast<string>().ToArray();
        if (!names.SequenceEqual(names.Order(StringComparer.Ordinal), StringComparer.Ordinal)
            || names.Distinct(StringComparer.Ordinal).Count() != names.Length)
            throw new FileMapParseException(location, "include names must be unique and ordinally sorted");
        if (!root.Table.TryGetValue("schema_version", out var version) || version is not (2L or 3L))
            throw new FileMapParseException(location, "include requires root schema_version 2 or 3");
        if (readInclude is null)
            throw new FileMapParseException(location, "include requires a reader for the same repository snapshot");

        foreach (var name in names)
        {
            var path = "Meta/" + name;
            byte[] includedBytes;
            try
            {
                includedBytes = readInclude(path);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or KeyNotFoundException)
            {
                throw new FileMapParseException(path, "included file is unavailable in this snapshot", exception);
            }

            RequireCanonicalBytes(includedBytes, path);
            var document = Decode(includedBytes, path);
            if (document.Table.Keys.Order(StringComparer.Ordinal).SequenceEqual(["files", "schema_version"])
                && document.Table["schema_version"] is 2L)
            {
                _ = FileMapTomlTables.Parse(document.Table["files"], path, allowEmpty: false);
                documents.Add(document);
            }
            else
                throw new FileMapParseException(path,
                    "included files require exactly schema_version = 2 and nonempty files tables; nested include and residence_policy are not allowed");
        }

        return documents.ToImmutable();
    }

    internal static void RequireCanonicalBytes(ReadOnlySpan<byte> bytes, string location)
    {
        if (bytes.StartsWith(new byte[] { 0xEF, 0xBB, 0xBF }))
            throw new FileMapParseException(location, "bytes contain a UTF-8 BOM");
        if (bytes.IsEmpty || bytes[^1] != (byte)'\n' || bytes.Contains((byte)'\r'))
            throw new FileMapParseException(location, "bytes must be strict UTF-8 without BOM/CR and end in LF");
    }

    private static FileMapDocument Decode(ReadOnlySpan<byte> bytes, string location)
    {
        try
        {
            var text = StrictUtf8.GetString(bytes);
            _ = SyntaxParser.ParseStrict(text, location, validate: true);
            var table = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw new FileMapParseException(location, "TOML decoded to null");
            return new(location, ImmutableArray.Create(bytes.ToArray()), table);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FileMapParseException(location, "bytes are not strict UTF-8", exception);
        }
        catch (TomlException exception)
        {
            throw new FileMapParseException(location, $"invalid TOML: {exception.Message}", exception);
        }
    }
}
