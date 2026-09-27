using System.Text.RegularExpressions;

namespace StrataLint.EngineeringScope;

internal static partial class CompilationProof
{
    internal static bool ValidateCapability(int exit, string output) =>
        exit == 1 && CapabilityDiagnostic().IsMatch(output)
        && Errors(output).All(line => line.Contains(": error CS7036:", StringComparison.Ordinal));

    internal static bool ValidateBannedApi(int exit, string output, string source)
    {
        var expected = source.Split('\n').Select((line, index) => (line, index))
            .Where(item => item.line.Contains("// banned-api-proof", StringComparison.Ordinal)).Select(item => item.index + 1).ToArray();
        var actual = BannedDiagnostic().Matches(output).Select(match => int.Parse(match.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture)).Distinct().Order().ToArray();
        return exit == 1 && expected.Length > 0 && expected.SequenceEqual(actual)
            && Errors(output).All(line => line.Contains(": error RS0030:", StringComparison.Ordinal));
    }

    private static IEnumerable<string> Errors(string output) => output.Split('\n').Where(line => line.Contains(": error ", StringComparison.Ordinal));

    [GeneratedRegex(@"MissingCapability\.cs\(\d+,\d+\): error CS7036:[^\r\n]*\bmetaClear\b")]
    private static partial Regex CapabilityDiagnostic();

    [GeneratedRegex(@"BannedApiViolations\.cs\((\d+),\d+\): error RS0030:")]
    private static partial Regex BannedDiagnostic();
}
