using System.Reflection;

namespace StrataLint.Scribe;

internal static class ScribeResourceCommands
{
    private const string Usage = "usage: resources pack --out <file> | resources verify --pack <file>";

    internal static int Run(Assembly assembly, IReadOnlyList<string> arguments, string workingDirectory,
        Func<string> repositoryRoot, TextWriter output, TextWriter error)
    {
        if (arguments.Count != 4
            || arguments[1] is not ("pack" or "verify")
            || arguments[2] != (arguments[1] == "pack" ? "--out" : "--pack")
            || string.IsNullOrWhiteSpace(arguments[3]))
        {
            error.WriteLine(Usage);
            return 2;
        }

        try
        {
            var path = Path.GetFullPath(arguments[3], workingDirectory);
            var root = repositoryRoot();
            if (arguments[1] == "pack")
            {
                var manifest = ScribeResourcePack.Write(path, DocumentDefinitions.Discover(assembly, root));
                output.WriteLine(FormattableString.Invariant(
                    $"resources pack: entries={manifest.EntryCount} uncompressedBytes={manifest.TotalUncompressedBytes} totalSha256={manifest.TotalSha256}"));
                return 0;
            }

            var pack = ScribeResourcePack.Open(path);
            var definitions = DocumentDefinitions.Discover(assembly, root)
                .ToDictionary(item => item.Document.Header.Gid.Value, StringComparer.Ordinal);
            var mismatches = 0;
            foreach (var entry in pack.Manifest.Entries)
            {
                _ = pack.Read(entry.Gid);
                if (!definitions.Remove(entry.Gid, out var current))
                {
                    mismatches++;
                    error.WriteLine($"Unexpected definition: {entry.Gid}");
                }
                else if (!pack.EncodedBytes(entry.Gid).SequenceEqual(ScribeResourceCodec.Encode(current)))
                {
                    mismatches++;
                    error.WriteLine($"Canonical content differs: {entry.Gid}");
                }
            }
            foreach (var gid in definitions.Keys.Order(StringComparer.Ordinal))
            {
                mismatches++;
                error.WriteLine($"Missing definition: {gid}");
            }
            output.WriteLine(FormattableString.Invariant(
                $"resources verify: entries={pack.Manifest.EntryCount} mismatches={mismatches}"));
            return mismatches == 0 ? 0 : 1;
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or FormatException or InvalidOperationException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }
}
