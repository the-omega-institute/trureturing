namespace StrataLint.Cli;

internal enum OleanWarmth
{
    Cold,
    Warm,
    ProbeFailed,
}

internal sealed record OleanWarmthInspection(OleanWarmth State, string? Error)
{
    internal bool IsWarm => State == OleanWarmth.Warm;
}

internal sealed record ContentRootInspection(bool Clear, string? Error);

internal interface ILeanCacheStateProbe
{
    OleanWarmthInspection ProbeOleans(string root);

    ContentRootInspection InspectContentRoot(string root);
}

internal sealed class FileSystemLeanCacheStateProbe : ILeanCacheStateProbe
{
    internal static FileSystemLeanCacheStateProbe Instance { get; } = new();

    private FileSystemLeanCacheStateProbe()
    {
    }

    public OleanWarmthInspection ProbeOleans(string root)
    {
        try
        {
            var rootState = InspectPath(root);
            if (rootState == PathState.Absent)
            {
                return new OleanWarmthInspection(OleanWarmth.Cold, null);
            }
            if (rootState != PathState.Directory)
            {
                return FailedOleanProbe(root, "olean root is not a private directory");
            }

            var pending = new Stack<string>();
            pending.Push(root);
            while (pending.Count > 0)
            {
                foreach (var entry in Directory.EnumerateFileSystemEntries(pending.Pop()))
                {
                    var state = InspectPath(entry);
                    if (state == PathState.Directory)
                    {
                        pending.Push(entry);
                        continue;
                    }
                    if (state == PathState.RegularFile
                        && string.Equals(Path.GetExtension(entry), ".olean", StringComparison.Ordinal))
                    {
                        return new OleanWarmthInspection(OleanWarmth.Warm, null);
                    }
                }
            }

            return new OleanWarmthInspection(OleanWarmth.Cold, null);
        }
        catch (Exception exception) when (IsEnumerationFailure(exception))
        {
            return FailedOleanProbe(root, exception.Message);
        }
    }

    public ContentRootInspection InspectContentRoot(string root)
    {
        try
        {
            var rootState = InspectPath(root);
            if (rootState == PathState.Absent) return new ContentRootInspection(true, null);
            if (rootState != PathState.Directory)
            {
                return new ContentRootInspection(false, "content root is not a private directory");
            }

            var pending = new Stack<string>();
            pending.Push(root);
            while (pending.Count > 0)
            {
                foreach (var entry in Directory.EnumerateFileSystemEntries(pending.Pop()))
                {
                    if (InspectPath(entry) is PathState.Directory)
                    {
                        pending.Push(entry);
                        continue;
                    }
                    return new ContentRootInspection(
                        false,
                        $"content root contains an existing entry: {entry}");
                }
            }

            return new ContentRootInspection(true, null);
        }
        catch (Exception exception) when (IsEnumerationFailure(exception))
        {
            return new ContentRootInspection(
                false,
                $"content root enumeration failed: {exception.Message}");
        }
    }

    private static PathState InspectPath(string path)
    {
        FileAttributes attributes;
        try
        {
            attributes = File.GetAttributes(path);
        }
        catch (Exception exception) when (exception is FileNotFoundException
            or DirectoryNotFoundException)
        {
            return PathState.Absent;
        }

        if (attributes.HasFlag(FileAttributes.ReparsePoint)) return PathState.Other;
        if (attributes.HasFlag(FileAttributes.Directory)) return PathState.Directory;
        return File.Exists(path) ? PathState.RegularFile : PathState.Other;
    }

    private static OleanWarmthInspection FailedOleanProbe(string root, string error) =>
        new(OleanWarmth.ProbeFailed, $"olean enumeration failed at {root}: {error}");

    private static bool IsEnumerationFailure(Exception exception) => exception is IOException
        or UnauthorizedAccessException
        or InvalidOperationException
        or System.Security.SecurityException;

    private enum PathState
    {
        Absent,
        Directory,
        RegularFile,
        Other,
    }
}
