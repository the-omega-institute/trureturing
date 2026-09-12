namespace StrataLint.Cli;

internal sealed record ContentRootInspection(bool Clear, string? Error);

internal static class LeanCacheStateProbe
{
    internal static ContentRootInspection InspectContentRoot(string root)
    {
        try
        {
            _ = File.GetAttributes(root);
            return new(false, "content root already exists");
        }
        catch (Exception exception) when (exception is FileNotFoundException or DirectoryNotFoundException)
        {
            return new(true, null);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            return new(false, "content root inspection failed: " + exception.Message);
        }
    }
}
