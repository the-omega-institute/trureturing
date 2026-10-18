using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using Tomlyn.Model;

namespace StrataLint.Engine;

internal sealed class FileMapPatternException(string pattern)
    : FormatException($"unsafe FILEMAP pattern: {pattern}")
{
    internal const string FindingCode = "FILEMAP-PATTERN-UNSAFE";

    internal string Pattern { get; } = pattern;
}

internal sealed class FileMapGlob
{
    private static readonly ConcurrentDictionary<string, Lazy<FileMapGlob>> compiledPatterns = new(StringComparer.Ordinal);
    private readonly Regex regex;
    private readonly string literalPrefix;

    private FileMapGlob(string pattern, Regex regex)
    {
        Pattern = pattern;
        this.regex = regex;
        var wildcard = pattern.IndexOf('*');
        literalPrefix = wildcard < 0 ? pattern : pattern[..wildcard];
    }

    internal string Pattern { get; }

    // Every accepted match begins with this literal prefix. Keep the regex as
    // the final matcher, including its existing null-input diagnostic.
    internal bool IsMatch(string path) =>
        (path is null || path.StartsWith(literalPrefix, StringComparison.Ordinal)) && regex.IsMatch(path!);

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

        return GetOrCompile(pattern);
    }

    internal static FileMapGlob CreateForAdmissionPlane(string pattern)
    {
        if (pattern.Contains('?'))
        {
            throw new FileMapPatternException(pattern);
        }

        return GetOrCompile(pattern);
    }

    internal static ImmutableArray<string> ParseExclusions(TomlTable table, string location)
    {
        if (!table.TryGetValue("exclude", out var raw)) return [];
        if (raw is not TomlArray { Count: > 0 } array || array.Any(value => value is not string))
            throw new FileMapParseException(location, "exclude must be a non-empty string array");
        var values = array.Cast<string>().ToImmutableArray();
        if (!values.SequenceEqual(values.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)))
            throw new FileMapParseException(location, "exclude must be unique and ordinally sorted");
        foreach (var value in values) _ = Create(value);
        return values;
    }

    // Each entry validates before sharing the immutable compiled pattern.
    private static FileMapGlob GetOrCompile(string pattern) =>
        compiledPatterns.GetOrAdd(pattern, static value =>
            new Lazy<FileMapGlob>(() => Compile(value), LazyThreadSafetyMode.ExecutionAndPublication)).Value;

    private static FileMapGlob Compile(string pattern)
    {
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
