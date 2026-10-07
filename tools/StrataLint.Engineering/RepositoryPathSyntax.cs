namespace StrataLint.Engineering;

internal static class RepositoryPathSyntax
{
    internal static bool IsValid(string? value) =>
        !string.IsNullOrEmpty(value)
            && !value.StartsWith("/", StringComparison.Ordinal)
            && value.IndexOf('\\') < 0
            && value.IndexOf('\0') < 0
            && value.Split('/').All(static segment => segment.Length > 0 && segment is not "." and not "..");
}
