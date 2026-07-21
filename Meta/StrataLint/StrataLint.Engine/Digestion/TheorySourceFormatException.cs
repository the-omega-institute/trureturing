namespace StrataLint.Engine;

internal sealed class TheorySourceFormatException(string message) : FormatException(message)
{
    internal static string? IdentifyAt(
        Func<string, string?> identify,
        string value,
        int characterOffset,
        string source)
    {
        try
        {
            return identify(value);
        }
        catch (TheorySourceFormatException exception)
        {
            throw new TheorySourceFormatException(
                $"{exception.Message} at line {LineNumber(source, characterOffset)}");
        }
    }

    internal static string ClaimLead(string paragraph)
    {
        var start = paragraph.AsSpan().IndexOf("**", StringComparison.Ordinal);
        var end = paragraph.AsSpan(start + 2).IndexOf("**", StringComparison.Ordinal);
        return end < 0
            ? paragraph[start..].TrimEnd()
            : paragraph[start..(start + end + 4)];
    }

    private static int LineNumber(string source, int characterOffset)
    {
        var line = 1;
        for (var index = 0; index < characterOffset; index++)
        {
            if (source[index] == '\n'
                || source[index] == '\r'
                && (index + 1 >= characterOffset || source[index + 1] != '\n'))
            {
                line++;
            }
        }

        return line;
    }
}
