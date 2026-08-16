using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class TaskBlockReferenceSyntax
{
    private const string TaskTokenExpression = "TASK\\s+(?<code>D5-T[0-9]{4})";

    internal static readonly Regex TaskTokenPattern = new(
        TaskTokenExpression,
        RegexOptions.CultureInvariant);

    private static readonly Regex DocumentationCommentTaskPattern = new(
        "^[\\t ]*/--[\\t ]+" + TaskTokenExpression,
        RegexOptions.CultureInvariant | RegexOptions.Multiline);

    internal static int CountDocumentationCommentTaskStarts(string text, string caseId)
    {
        ArgumentNullException.ThrowIfNull(text);
        ArgumentException.ThrowIfNullOrWhiteSpace(caseId);

        return DocumentationCommentTaskPattern.Matches(text)
            .Count(match => string.Equals(
                match.Groups["code"].Value,
                caseId,
                StringComparison.Ordinal));
    }
}
