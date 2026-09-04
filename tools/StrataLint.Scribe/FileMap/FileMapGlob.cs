using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Scribe;

internal sealed class FileMapPatternException(string pattern)
    : FormatException($"unsafe FILEMAP pattern: {pattern}")
{
    internal const string FindingCode = "FILEMAP-PATTERN-UNSAFE";

    internal string Pattern { get; } = pattern;
}

internal sealed class FileMapGlob
{
    private readonly Regex regex;

    private FileMapGlob(string pattern, Regex regex)
    {
        Pattern = pattern;
        this.regex = regex;
    }

    internal string Pattern { get; }

    internal bool IsMatch(string path) => regex.IsMatch(path);

    internal static FileMapGlob Create(string pattern)
    {
        if (string.IsNullOrWhiteSpace(pattern)
            || !string.Equals(pattern, pattern.Trim(), StringComparison.Ordinal)
            || pattern[0] == '/'
            || pattern.Contains('\\')
            || pattern.Contains('?')
            || pattern.Contains("//", StringComparison.Ordinal)
            || pattern.Any(static character => character is < ' ' or > '~')
            || pattern.Split('/').Any(static segment => segment is "." or ".." or ""))
        {
            throw new FileMapPatternException(pattern);
        }

        var expression = new StringBuilder("\\A");
        for (var index = 0; index < pattern.Length; index++)
        {
            var character = pattern[index];
            if (character == '*' && index + 1 < pattern.Length && pattern[index + 1] == '*')
            {
                if (index + 2 < pattern.Length && pattern[index + 2] == '/')
                {
                    expression.Append("(?:.*/)?");
                    index += 2;
                }
                else
                {
                    expression.Append(".*");
                    index++;
                }

                continue;
            }

            expression.Append(character switch
            {
                '*' => "[^/]*",
                _ => Regex.Escape(character.ToString()),
            });
        }

        expression.Append("\\z");
        return new FileMapGlob(
            pattern,
            new Regex(
                expression.ToString(),
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking));
    }
}
