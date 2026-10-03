namespace StrataLint.Scribe;

internal static class ScribeResourceCommands
{
    internal const string Usage = "usage: resources pack --out <file> | resources verify --pack <file>"
        + " | resources release --out <directory>"
        + " | resources verify-release --dir <directory> [--total-sha256 <digest>]";

    internal static int Run(IReadOnlyList<string> arguments, string workingDirectory,
        Func<string> repositoryRoot, TextWriter output, TextWriter error)
    {
        if (arguments.Count > 1 && arguments[1] is "release" or "verify-release")
            return ScribeReleaseCommands.Run(arguments, workingDirectory, repositoryRoot, output, error);

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
            if (arguments[1] == "pack")
            {
                var result = ScribeResourceScriptPacker.Write(repositoryRoot(), path);
                if (!result.Failures.IsEmpty)
                {
                    foreach (var failure in result.Failures) error.WriteLine(failure);
                    return 1;
                }
                var manifest = result.Manifest!;
                var summary = FormattableString.Invariant(
                    $"resources pack: entries={manifest.EntryCount} uncompressedBytes={manifest.TotalUncompressedBytes} totalSha256={manifest.TotalSha256}");
                output.WriteLine(summary);
                return 0;
            }

            var pack = ScribeResourcePack.Open(path);
            foreach (var entry in pack.Manifest.Entries)
            {
                try
                {
                    _ = pack.Read(entry.Gid);
                }
                catch (ScribeResourceException exception)
                {
                    error.WriteLine($"{entry.Gid}: {exception.Message}");
                    return 1;
                }
            }
            output.WriteLine(FormattableString.Invariant(
                $"resources verify: entries={pack.Manifest.EntryCount} totalSha256={pack.Manifest.TotalSha256}"));
            return 0;
        }
        catch (ScribeResourcePackException exception) when (exception.ReasonCode is
            ScribeResourcePackErrorCode.EntryDigestMismatch or ScribeResourcePackErrorCode.TotalDigestMismatch)
        {
            error.WriteLine(exception.Message);
            return 1;
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or FormatException or InvalidOperationException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }
}
