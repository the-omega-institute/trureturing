using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineCapacityBehaviorTests
{
    private const string Project = "tools/tests/IoFixture/IoFixture.csproj";
    private const string Source = "tools/tests/IoFixture/IoTests.cs";
    private const string IoSource = """
        public class IoTests
        {
            [Xunit.Fact]
            public void ReadsFile()
            {
                var path = System.Environment.GetEnvironmentVariable("FIXTURE_INPUT");
                System.IO.File.ReadAllText(path!);
            }
        }
        """;

    [Fact]
    public void Sl003AcceptsValidIoTestWithoutParserDebt()
    {
        var fixture = IoFixture();
        Assert.DoesNotContain(CSharpSyntaxTree.ParseText(IoSource).GetDiagnostics(),
            diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);

        var result = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3),
            fixture.Build(RawChangeSet.Create([Source])));

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void Sl003StillRejectsLineCapacityGrowthInIoTest()
    {
        var fixture = IoFixture();
        fixture.Files[Source] += string.Concat(Enumerable.Repeat("// padding\n",
            RepositoryRules.ArtifactHardLineLimit));

        var result = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3),
            fixture.Build(RawChangeSet.Create([Source])));

        var finding = Assert.Single(result.Diagnostics);
        Assert.Equal(Source, finding.Path);
        Assert.Equal("artifact exceeds 800 lines", finding.Message);
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
    }

    [Fact]
    public void Sl003StillRejectsDirectoryCapacityGrowthWithIoTest()
    {
        var fixture = IoFixture();
        for (var index = 0; index < RepositoryRules.DirectoryFileLimit - 1; index++)
        {
            var path = $"tools/tests/IoFixture/Existing{index}.cs";
            fixture.Files[path] = fixture.Baseline[path] = "// fixture\n";
        }

        var result = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3),
            fixture.Build(RawChangeSet.Create([Source])));

        var finding = Assert.Single(result.Diagnostics);
        Assert.Equal("tools/tests/IoFixture", finding.Path);
        Assert.StartsWith("directory contains", finding.Message);
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
    }

    private static RuleFixture IoFixture()
    {
        var fixture = new RuleFixture();
        fixture.Files[Project] = fixture.Baseline[Project] = """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>
            <ItemGroup><PackageReference Include="xunit" Version="2.9.3" /></ItemGroup></Project>
            """;
        fixture.Files[Source] = IoSource;
        return fixture;
    }
}
