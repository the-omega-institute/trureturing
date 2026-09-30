using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class FileMapPlanningTests
{
    [Theory]
    [InlineData("missing-require")]
    [InlineData("unknown-resource")]
    [InlineData("cycle")]
    [InlineData("same-stage-cycle")]
    [InlineData("missing-material")]
    [InlineData("unregistered-owner")]
    [InlineData("invalid-owner")]
    [InlineData("name-newline")]
    [InlineData("numeric-projection-mode")]
    [InlineData("duplicate-resource")]
    [InlineData("duplicate-field")]
    [InlineData("invalid-stage")]
    [InlineData("invalid-cache")]
    [InlineData("retired-report-cache")]
    [InlineData("retired-activation")]
    [InlineData("missing-activation")]
    [InlineData("unknown-activation")]
    [InlineData("conflicting-activation")]
    [InlineData("extra-activation")]
    [InlineData("invalid-pattern")]
    [InlineData("invalid-mode")]
    public void InvalidDeclarationsFailInStrictLoader(string mutation)
    {
        var source = FileMapPlanningFixture.Canonical["filemap"]!.GetValue<string>();
        source = mutation switch
        {
            "missing-require" => source.Replace("require = []\n", "", StringComparison.Ordinal),
            "unknown-resource" => source.Replace("require = []", "require = [\"unknown\"]", StringComparison.Ordinal),
            "cycle" => source.Replace("prerequisites = []", "prerequisites = [\"engineering\"]", StringComparison.Ordinal),
            "same-stage-cycle" => source.Replace("prerequisites = []", "prerequisites = [\"lean-report\"]", StringComparison.Ordinal)
                .Replace("stage = \"build\"", "stage = \"current\"", StringComparison.Ordinal)
                .Replace("stage = \"engineering\"", "stage = \"current\"", StringComparison.Ordinal),
            "missing-material" => source.Replace("materials = []", "materials = [\"tools/missing.py\"]", StringComparison.Ordinal),
            "unregistered-owner" => source.Replace("owner = \"tools/owner.py\"", "owner = \"unregistered.py\"", StringComparison.Ordinal),
            "invalid-owner" => source.Replace("owner = \"tools/owner.py\"", "owner = \"tools/../README.md\"", StringComparison.Ordinal),
            "name-newline" => source.Replace("consumed_by = [\"reader\"]", "consumed_by = [\"reader\\n\"]", StringComparison.Ordinal),
            "numeric-projection-mode" => NumericProjectionMode(source),
            "duplicate-resource" => source.Replace("id = \"engineering\"", "id = \"build\"", StringComparison.Ordinal),
            "duplicate-field" => source.Replace("schema_version = 5", "schema_version = 5\nschema_version = 5", StringComparison.Ordinal),
            "invalid-stage" => source.Replace("stage = \"current\"", "stage = \"unknown\"", StringComparison.Ordinal),
            "invalid-cache" => source.Replace("cache_layers = []", "cache_layers = [\"unknown\"]", StringComparison.Ordinal),
            "retired-report-cache" => source.Replace("cache_layers = [], cache_activation = {}",
                "cache_layers = [\"report\"], cache_activation = {report = \"stage-start\"}", StringComparison.Ordinal),
            "retired-activation" => source.Replace("stage-start", "lean-production", StringComparison.Ordinal),
            "missing-activation" => source.Replace("cache_activation = {},", "", StringComparison.Ordinal),
            "unknown-activation" => source.Replace("stage-start", "unknown", StringComparison.Ordinal),
            "extra-activation" => source.Replace("cache_activation = {}", "cache_activation = {project = \"stage-start\"}", StringComparison.Ordinal),
            "conflicting-activation" => source.Replace("cache_layers = [], cache_activation = {}",
                "cache_layers = [\"project\"], cache_activation = {project = \"lean-production\"}", StringComparison.Ordinal),
            "invalid-pattern" => source.Replace("one/*.txt", "one/?.txt", StringComparison.Ordinal),
            _ => source + "mode = \"120000\"\n",
        };
        using var fixture = new FileMapPlanningFixture(source);
        if (mutation == "unregistered-owner") { fixture.Write("unregistered.py", "# unregistered\n"); fixture.Save(); }
        // The write-set operation uses the real strict loader without unrelated
        // whole-repository policy findings from this deliberately small fixture.
        Assert.Equal(2, FileMapConformCommand.Run(["--producer-write-set", "none"], fixture.Root).ExitCode);
    }

    [Fact]
    public void DeclaredUnicodeMaterialsAreAcceptedByStrictLoader()
    {
        const string first = "tools/material-\U0001F600";
        const string second = "tools/material-\uE000";
        var source = FileMapPlanningFixture.Canonical["filemap"]!.GetValue<string>()
            .Replace("materials = []", $"materials = [\"{first}\", \"{second}\"]", StringComparison.Ordinal);
        using var fixture = new FileMapPlanningFixture(source);
        fixture.Write(first, "first\n"); fixture.Write(second, "second\n"); fixture.Save();
        Assert.Equal(0, FileMapConformCommand.Run(["--producer-write-set", "none"], fixture.Root).ExitCode);
    }

    private static string NumericProjectionMode(string source)
    {
        var last = source.LastIndexOf("[[files]]", StringComparison.Ordinal);
        return source[..last] + source[last..]
            .Replace("kind = \"program\"", "kind = \"generated\"", StringComparison.Ordinal)
            .Replace("produced_by = \"none\"", "produced_by = \"FixtureProducer\"", StringComparison.Ordinal)
            .Replace("verified_by = [\"dotnet-test\"]", "verified_by = [\"FixtureProducer\"]", StringComparison.Ordinal)
            .Replace("artifact_id = \"none\"", "artifact_id = \"fixture-artifact\"", StringComparison.Ordinal)
            + "mode = 100644\nhistory_requirement = \"not-required\"\n";
    }
}
