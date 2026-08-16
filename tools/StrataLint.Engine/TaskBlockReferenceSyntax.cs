using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class TaskBlockReferenceSyntax
{
    // RepositoryRules consumes this exact dev token grammar; MISSION tightens it below.
    private const string TaskTokenExpression = "TASK\\s+(?<code>D5-T[0-9]{4})";

    internal static readonly Regex TaskTokenPattern = new(
        TaskTokenExpression,
        RegexOptions.CultureInvariant);

    private const string MissionTaskTokenExpression =
        TaskTokenExpression + "(?![0-9])";

    private static readonly Regex DocumentationCommentTaskPattern = new(
        "^[\\t ]*(?<open>/--)[\\t ]+" + MissionTaskTokenExpression,
        RegexOptions.CultureInvariant | RegexOptions.Multiline);

    internal static int CountDocumentationCommentTaskStarts(string text, string caseId)
    {
        ArgumentNullException.ThrowIfNull(text);
        ArgumentException.ThrowIfNullOrWhiteSpace(caseId);

        var activeStarts = CollectTopLevelDocumentationCommentStarts(text);
        return DocumentationCommentTaskPattern.Matches(text)
            .Count(match => activeStarts.Contains(match.Groups["open"].Index)
                && string.Equals(
                    match.Groups["code"].Value,
                    caseId,
                    StringComparison.Ordinal));
    }

    private static HashSet<int> CollectTopLevelDocumentationCommentStarts(string text)
    {
        var starts = new HashSet<int>();
        var blockCommentDepth = 0;
        var inLineComment = false;
        var inString = false;

        for (var index = 0; index < text.Length; index++)
        {
            var current = text[index];
            var next = index + 1 < text.Length ? text[index + 1] : '\0';

            if (blockCommentDepth > 0)
            {
                if (current == '/' && next == '-')
                {
                    blockCommentDepth++;
                    index++;
                }
                else if (current == '-' && next == '/')
                {
                    blockCommentDepth--;
                    index++;
                }

                continue;
            }

            if (inLineComment)
            {
                if (current == '\n')
                {
                    inLineComment = false;
                }

                continue;
            }

            if (inString)
            {
                if (current == '\\' && index + 1 < text.Length)
                {
                    index++;
                }
                else if (current == '"')
                {
                    inString = false;
                }

                continue;
            }

            if (current == '"')
            {
                inString = true;
            }
            else if (current == '-' && next == '-')
            {
                inLineComment = true;
                index++;
            }
            else if (current == '/' && next == '-')
            {
                if (index + 2 < text.Length && text[index + 2] == '-')
                {
                    starts.Add(index);
                }

                blockCommentDepth = 1;
                index++;
            }
        }

        return starts;
    }
}
