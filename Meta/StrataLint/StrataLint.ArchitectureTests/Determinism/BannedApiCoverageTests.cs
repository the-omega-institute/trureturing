namespace StrataLint.ArchitectureTests;

public sealed class BannedApiCoverageTests
{
    private static readonly string[] NumericTypes =
    [
        "System.Byte",
        "System.SByte",
        "System.Int16",
        "System.UInt16",
        "System.Int32",
        "System.UInt32",
        "System.Int64",
        "System.UInt64",
        "System.Int128",
        "System.UInt128",
        "System.Half",
        "System.Single",
        "System.Double",
        "System.Decimal",
    ];

    [Fact]
    public void BannedSymbolsCoverTheExplicitProviderlessCultureMatrix()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "Meta",
            "StrataLint",
            "Architecture",
            "BannedSymbols.txt");
        var actual = File.ReadLines(path)
            .Where(static line => !string.IsNullOrWhiteSpace(line))
            .Select(static line => line.Split(';', 2)[0])
            .ToHashSet(StringComparer.Ordinal);
        var expected = RequiredCultureSensitiveMembers().ToArray();
        var missing = expected.Where(member => !actual.Contains(member)).ToArray();

        Assert.Equal(143, expected.Length);
        Assert.True(missing.Length == 0, "Missing banned symbols:\n" + string.Join("\n", missing));
    }

    [Fact]
    public void CompileFailProofMarksEveryExpectedDiagnosticLine()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "Meta",
            "StrataLint",
            "BannedApiCompileFailProof",
            "BannedApiViolations.cs");

        Assert.Equal(18, File.ReadLines(path).Count(static line =>
            line.Contains("// banned-api-proof", StringComparison.Ordinal)));
    }

    [Fact]
    public void EngineeringCiComparesEveryMarkedLineWithAnRs0030Diagnostic()
    {
        var path = Path.Combine(RepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml");
        var workflow = File.ReadAllText(path);

        Assert.Contains("mapfile -t expected_lines", workflow, StringComparison.Ordinal);
        Assert.Contains("grep -nF \"// banned-api-proof\"", workflow, StringComparison.Ordinal);
        Assert.Contains("mapfile -t actual_lines", workflow, StringComparison.Ordinal);
        Assert.Contains("error RS0030", workflow, StringComparison.Ordinal);
        Assert.Contains(
            "test \"${#actual_lines[@]}\" -eq \"${#expected_lines[@]}\"",
            workflow,
            StringComparison.Ordinal);
    }

    private static IEnumerable<string> RequiredCultureSensitiveMembers()
    {
        foreach (var type in NumericTypes)
        {
            yield return $"M:{type}.Parse(System.String)";
            yield return $"M:{type}.Parse(System.String,System.Globalization.NumberStyles)";
            yield return $"M:{type}.ToString";
            yield return $"M:{type}.ToString(System.String)";
            yield return $"M:{type}.TryParse(System.ReadOnlySpan{{System.Byte}},{type}@)";
            yield return $"M:{type}.TryParse(System.ReadOnlySpan{{System.Char}},{type}@)";
            yield return $"M:{type}.TryParse(System.String,{type}@)";
        }

        const string bigInteger = "System.Numerics.BigInteger";
        yield return $"M:{bigInteger}.Parse(System.String)";
        yield return $"M:{bigInteger}.Parse(System.String,System.Globalization.NumberStyles)";
        yield return $"M:{bigInteger}.ToString";
        yield return $"M:{bigInteger}.ToString(System.String)";
        yield return $"M:{bigInteger}.TryParse(System.ReadOnlySpan{{System.Char}},{bigInteger}@)";
        yield return $"M:{bigInteger}.TryParse(System.String,{bigInteger}@)";

        foreach (var type in new[] { "System.DateTime", "System.DateTimeOffset", "System.TimeSpan" })
        {
            yield return $"M:{type}.Parse(System.String)";
            yield return $"M:{type}.ToString";
            yield return $"M:{type}.ToString(System.String)";
            yield return $"M:{type}.TryParse(System.ReadOnlySpan{{System.Char}},{type}@)";
            yield return $"M:{type}.TryParse(System.String,{type}@)";
        }

        foreach (var type in new[] { "System.DateOnly", "System.TimeOnly" })
        {
            yield return $"M:{type}.Parse(System.String)";
            yield return $"M:{type}.ParseExact(System.ReadOnlySpan{{System.Char}},System.String[])";
            yield return $"M:{type}.ParseExact(System.String,System.String)";
            yield return $"M:{type}.ParseExact(System.String,System.String[])";
            yield return $"M:{type}.ToString";
            yield return $"M:{type}.ToString(System.String)";
            yield return $"M:{type}.TryParse(System.ReadOnlySpan{{System.Char}},{type}@)";
            yield return $"M:{type}.TryParse(System.String,{type}@)";
            yield return $"M:{type}.TryParseExact(System.ReadOnlySpan{{System.Char}},System.ReadOnlySpan{{System.Char}},{type}@)";
            yield return $"M:{type}.TryParseExact(System.ReadOnlySpan{{System.Char}},System.String[],{type}@)";
            yield return $"M:{type}.TryParseExact(System.String,System.String,{type}@)";
            yield return $"M:{type}.TryParseExact(System.String,System.String[],{type}@)";
        }
    }
}
