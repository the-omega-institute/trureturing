using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class AffectedBoundaryTests
{
    [Fact]
    public void ExplicitValuesCoversConstantInlineRowsAndLocalCapturedProviders()
    {
        using var fixture = new AffectedExecutionFixture();
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", """
            namespace First;
            public class Tests {
                private readonly int value = 7;
                [Xunit.Theory] [Xunit.InlineData(1)] [Xunit.InlineData(2)]
                public void Runs(int row) {
                    var captured = value + row;
                    System.Func<int> provider = () => Helper(captured);
                    Xunit.Assert.Equal(7 + row, provider());
                }
                private static int Helper(int input) => input;
            }
            """);
        var cold = fixture.Tests(fixture.Build());
        Assert.Equal(3, cold.Projects.Sum(project => project.Executed));
        var action = fixture.Plan().Actions[0];
        var source = cold.Projects[0].Coverage[0].Source;
        var originalTrx = Path.Combine(fixture.Root, source.Trx[0].Path);
        foreach (var mutation in new[] { "missing", "extra", "multiplicity" })
        {
            var document = System.Xml.Linq.XDocument.Load(originalTrx);
            var resultRows = document.Descendants().Where(element => element.Name.LocalName == "UnitTestResult").ToArray();
            var definitions = document.Descendants().Where(element => element.Name.LocalName == "UnitTest").ToArray();
            var count = resultRows.Length;
            if (mutation == "missing")
            {
                var id = resultRows[1].Attribute("testId")!.Value;
                definitions.Single(item => item.Attribute("id")!.Value == id).Remove();
                resultRows[1].Remove(); count--;
            }
            else if (mutation == "extra")
            {
                var id = Guid.NewGuid().ToString();
                var clone = new System.Xml.Linq.XElement(resultRows[0]); clone.SetAttributeValue("testId", id);
                resultRows[0].Parent!.Add(clone);
                var definition = new System.Xml.Linq.XElement(definitions.Single(item => item.Attribute("id")!.Value == resultRows[0].Attribute("testId")!.Value));
                definition.SetAttributeValue("id", id); definitions[0].Parent!.Add(definition); count++;
            }
            else resultRows[1].SetAttributeValue("testName", resultRows[0].Attribute("testName")!.Value);
            var counters = document.Descendants().Single(element => element.Name.LocalName == "Counters");
            foreach (var name in new[] { "total", "executed", "passed" }) counters.SetAttributeValue(name, count);
            var path = "build/ci/negative-rows/" + mutation + "/source.trx";
            fixture.Write(path, document.ToString());
            var materials = CommonExecutionEvidence.Materials(fixture.Root, [path]);
            Assert.Throws<InvalidDataException>(() => AffectedTestCache.ValidateSource(action,
                source with { Covered = count, Trx = materials }, [Path.Combine(fixture.Root, path)]));
        }
        fixture.Write("README.md", "unrelated candidate\n");
        var build = fixture.Build();
        var warm = fixture.Tests(build);
        Assert.Equal(0, warm.Projects.Sum(project => project.Executed));
        Assert.Equal(2, Assert.Single(warm.Projects[0].Coverage).Covered);
        Assert.Equal(cold.Round, warm.Projects[0].Coverage[0].Source.Round);
        CommonExecutionEvidence.ValidateTests(fixture.Root);
        fixture.ClearSeed();
        Assert.Equal(3, fixture.Tests(build).Projects.Sum(project => project.Executed));
    }

    [Fact]
    public void FiniteMembershipAndOwnerChangesRequireFreshWholeProjectExecution()
    {
        using var fixture = new AffectedExecutionFixture();
        const string path = "tools/tests/StrataLint.First/Tests.cs";
        const string fact = "[Xunit.Fact] public void Runs() { Xunit.Assert.True(true); }";
        const string inline = "[Xunit.Theory] [Xunit.InlineData(1)] [Xunit.InlineData(2)] public void Row(int value) { Xunit.Assert.True(value > 0); }";
        void Source(string members) => fixture.Write(path, "namespace First; public class Tests { " + members + " }");
        Source(fact + inline);
        var cold = fixture.Tests(fixture.Build());
        Assert.Equal(4, cold.Projects.Sum(project => project.Executed));
        foreach (var (members, count) in new[] { (inline, 2), (inline.Replace("Row(", "Renamed(", StringComparison.Ordinal), 2),
                     (inline.Replace("InlineData(2)", "InlineData(3)", StringComparison.Ordinal), 2),
                     (inline + fact, 3), (inline.Replace("[Xunit.InlineData(2)]", "", StringComparison.Ordinal) + fact, 2) })
        {
            Source(members);
            var result = fixture.Tests(fixture.Build());
            Assert.Equal(count, result.Projects[0].Executed);
            Assert.Equal(0, result.Projects[1].Executed);
            Assert.Equal("executed", Assert.Single(result.Projects[0].Coverage).Status);
        }
        var originalSeed = File.ReadAllBytes(Path.Combine(fixture.CacheDirectory, "seed.json"));
        Source(inline + fact + "[Xunit.Fact] public void AddedFailure() { Xunit.Assert.True(false); }");
        var failed = fixture.Tests(fixture.Build(), expectedExit: 1);
        Assert.NotNull(failed.Projects[0].Error);
        Assert.DoesNotContain(failed.Projects[0].Coverage, row => row.Status == "reused");
        Assert.Equal(originalSeed, File.ReadAllBytes(Path.Combine(fixture.CacheDirectory, "seed.json")));
        Source(inline + fact);
        fixture.Tests(fixture.Build());
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        var owner = AffectedExecutionFixture.Owner(AffectedExecutionFixture.First);
        foreach (var declaration in new[] { "", owner.Replace("version = 1", "version = 2", StringComparison.Ordinal),
                     owner.Replace("AffectedTestCache.ValidateSource", "MissingVerifier.ValidateSource", StringComparison.Ordinal) })
        {
            fixture.Write("Meta/FILEMAP.toml", map.Replace(owner, declaration, StringComparison.Ordinal));
            var result = fixture.Tests(fixture.Build());
            Assert.Equal(3, result.Projects[0].Executed);
            Assert.Equal(0, result.Projects[1].Executed);
            Assert.Null(fixture.Plan().Actions[0].Binding);
        }
    }

    [Theory]
    [InlineData("helper")]
    [InlineData("callback")]
    [InlineData("module-initializer")]
    public void AmbientProvidersExecuteAfterEnvironmentChangesWithUnchangedDll(string form)
    {
        const string variable = "AFFECTED_PROVIDER_INPUT";
        var previous = Environment.GetEnvironmentVariable(variable);
        try
        {
            Environment.SetEnvironmentVariable(variable, "pass");
            using var fixture = new AffectedExecutionFixture();
            var expression = form == "helper" ? "Read()" : "new System.Func<string>(() => Read())()";
            fixture.Write("tools/tests/StrataLint.First/Tests.cs", $$"""
                namespace First; public class Tests {
                    [Xunit.Fact] public void Runs() { Xunit.Assert.Equal("pass", {{expression}}); }
                    private static string Read() => System.Environment.GetEnvironmentVariable("AFFECTED_PROVIDER_INPUT");
                }
                """);
            if (form == "module-initializer")
                fixture.Write("tools/tests/StrataLint.First/Tests.cs", """
                    namespace First; public class Tests {
                        internal static string Value;
                        [Xunit.Fact] public void Runs() { Xunit.Assert.Equal("pass", Value); }
                    }
                    internal static class Startup {
                        [System.Runtime.CompilerServices.ModuleInitializer]
                        internal static void Initialize() { Tests.Value = System.Environment.GetEnvironmentVariable("AFFECTED_PROVIDER_INPUT"); }
                    }
                    """);
            var build = fixture.Build();
            fixture.Tests(build);
            var dll = Path.Combine(fixture.Root, "tools/tests/StrataLint.First/bin/Release/net10.0/StrataLint.First.dll");
            var identity = CommonExecutionEvidence.Hash(dll);
            Environment.SetEnvironmentVariable(variable, "fail");
            var affected = fixture.Tests(build, expectedExit: 1);
            Assert.Equal(identity, CommonExecutionEvidence.Hash(dll));
            Assert.NotNull(affected.Projects[0].Error);
            Assert.Equal(0, affected.Projects[1].Executed);
            Assert.Contains(fixture.Plan().Actions[0].Unknown, item => item.Contains(form == "module-initializer" ? "module-initializer" : "Environment.GetEnvironmentVariable", StringComparison.Ordinal));
            fixture.ClearSeed();
            var full = fixture.Tests(build, expectedExit: 1);
            Assert.Equal(affected.Projects.Select(p => p.Exit), full.Projects.Select(p => p.Exit));
        }
        finally { Environment.SetEnvironmentVariable(variable, previous); }
    }

    [Fact]
    public void SerializerPropertyAmbientInputCannotReuseAfterFileRemoval()
    {
        using var fixture = new AffectedExecutionFixture();
        var path = Path.Combine(fixture.Root, "local-runtime/property-input");
        fixture.Write("local-runtime/property-input", "7");
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", $$"""
            namespace First;
            public class Tests {
                [Xunit.Fact] public void Runs() {
                    Xunit.Assert.Equal("{\"Present\":true}", System.Text.Json.JsonSerializer.Serialize(new Value()));
                }
            }
            public sealed class Value {
                public bool Present => System.IO.File.Exists({{System.Text.Json.JsonSerializer.Serialize(path)}});
            }
            """);
        var build = fixture.Build();
        fixture.Tests(build);
        var dll = Path.Combine(fixture.Root, "tools/tests/StrataLint.First/bin/Release/net10.0/StrataLint.First.dll");
        var identity = CommonExecutionEvidence.Hash(dll);
        fixture.Remove("local-runtime/property-input");
        var affected = fixture.Tests(build, expectedExit: 1);
        Assert.Equal(identity, CommonExecutionEvidence.Hash(dll));
        Assert.NotNull(affected.Projects[0].Error);
        Assert.Equal(0, affected.Projects[1].Executed);
        fixture.ClearSeed();
        var full = fixture.Tests(build, expectedExit: 1);
        Assert.Equal(affected.Projects.Select(p => p.Exit), full.Projects.Select(p => p.Exit));
    }

    [Fact]
    public void CustomValueConverterRemainsAnUnresolvedProvider()
    {
        using var fixture = new AffectedExecutionFixture();
        var path = Path.Combine(fixture.Root, "local-runtime/converter-input");
        fixture.Write("local-runtime/converter-input", "7");
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", $$"""
            namespace First;
            public class Tests {
                [Xunit.Fact] public void Runs() {
                    Xunit.Assert.Equal("true", System.Text.Json.JsonSerializer.Serialize(new Value()));
                }
            }
            [System.Text.Json.Serialization.JsonConverter(typeof(Converter))]
            public sealed class Value { }
            public sealed class Converter : System.Text.Json.Serialization.JsonConverter<Value> {
                public override Value Read(ref System.Text.Json.Utf8JsonReader reader, System.Type type,
                    System.Text.Json.JsonSerializerOptions options) => throw new System.NotSupportedException();
                public override void Write(System.Text.Json.Utf8JsonWriter writer, Value value,
                    System.Text.Json.JsonSerializerOptions options) => writer.WriteBooleanValue(
                        System.IO.File.Exists({{System.Text.Json.JsonSerializer.Serialize(path)}}));
            }
            """);
        var build = fixture.Build();
        fixture.Tests(build);
        fixture.Remove("local-runtime/converter-input");
        var failed = fixture.Tests(build, expectedExit: 1);
        Assert.NotNull(failed.Projects[0].Error);
        Assert.Equal(0, failed.Projects[1].Executed);
        Assert.Contains(fixture.Plan().Actions[0].Unknown, reason => reason.StartsWith("binding:custom-value-metadata:", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("System.IO.File.ReadAllBytes(path).Length == 1")]
    [InlineData("System.IO.File.Exists(path)")]
    [InlineData("System.Linq.Enumerable.Any(System.IO.Directory.EnumerateFiles(System.IO.Path.GetDirectoryName(path)))")]
    public void PhysicalQueriesRemainUnownedWhenMembershipOrRootDisappears(string query)
    {
        using var fixture = new AffectedExecutionFixture();
        var path = Path.Combine(fixture.Root, "local-runtime/query/value");
        fixture.Write("local-runtime/query/value", "7");
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", $$"""
            namespace First; public class Tests {
                [Xunit.Fact] public void Runs() {
                    var path = {{System.Text.Json.JsonSerializer.Serialize(path)}};
                    System.Func<bool> provider = () => {{query}};
                    Xunit.Assert.True(provider());
                }
            }
            """);
        var build = fixture.Build();
        fixture.Tests(build);
        var dll = Path.Combine(fixture.Root, "tools/tests/StrataLint.First/bin/Release/net10.0/StrataLint.First.dll");
        var identity = CommonExecutionEvidence.Hash(dll);
        fixture.Remove("local-runtime/query/value");
        var missingMember = fixture.Tests(build, expectedExit: 1);
        Assert.NotNull(missingMember.Projects[0].Error);
        Directory.Delete(Path.GetDirectoryName(path)!);
        var missingRoot = fixture.Tests(build, expectedExit: 1);
        Assert.NotNull(missingRoot.Projects[0].Error);
        Assert.Equal(identity, CommonExecutionEvidence.Hash(dll));
        Assert.Equal(0, missingRoot.Projects[1].Executed);
        Assert.NotEmpty(fixture.Plan().Actions[0].Unknown);
    }

    [Fact]
    public void UnsetLanguageSurvivesSealingExecutorAndDownstreamVerification()
    {
        var previous = Environment.GetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE");
        var culture = System.Globalization.CultureInfo.CurrentCulture;
        var uiCulture = System.Globalization.CultureInfo.CurrentUICulture;
        try
        {
            Environment.SetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE", null);
            using var fixture = new AffectedExecutionFixture();
            AffectedEnvironmentObservation.Write(fixture.Root, "fixture-after-unset");
            var child = CommonStages.TestEnvironment(fixture.Root);
            Assert.Equal("en-US", child.UICulture);
            System.Globalization.CultureInfo.CurrentCulture = new("fr-FR");
            System.Globalization.CultureInfo.CurrentUICulture = new("tr-TR");
            var repeated = CommonStages.TestEnvironment(fixture.Root);
            Assert.Equal(child.Identity, repeated.Identity);
            Assert.Equal(child.Culture, repeated.Culture);
            Assert.Equal(child.UICulture, repeated.UICulture);
            var build = fixture.Build();
            Assert.Null(Environment.GetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE"));
            var launch = CommonStages.TestEnvironment(fixture.Root);
            Assert.All(fixture.Plan().Actions, action => Assert.Equal(launch.ValuesIdentity, action.Environment));
            var cold = fixture.Tests(build, subprocess: true);
            Assert.Equal(2, cold.Projects.Sum(project => project.Executed));
            CommonExecutionEvidence.ValidateTests(fixture.Root);
            fixture.VerifyTestHostCultures(child.Culture, child.UICulture);
            var warm = fixture.Tests(build, subprocess: true);
            Assert.Equal(0, warm.Projects.Sum(project => project.Executed));
            Assert.All(warm.Projects.SelectMany(project => project.Coverage), coverage =>
            {
                Assert.Equal("reused", coverage.Status);
                Assert.Equal(cold.Round, coverage.Source.Round);
            });
            CommonExecutionEvidence.ValidateTests(fixture.Root);
            fixture.ClearSeed();
            var full = fixture.Tests(build, subprocess: true);
            Assert.Equal(2, full.Projects.Sum(project => project.Executed));
            Assert.Equal(warm.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
            Assert.Equal(2, warm.Projects.SelectMany(project => project.Coverage).Sum(coverage => coverage.Covered));
        }
        finally
        {
            Environment.SetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE", previous);
            System.Globalization.CultureInfo.CurrentCulture = culture;
            System.Globalization.CultureInfo.CurrentUICulture = uiCulture;
        }
    }

    [Fact]
    public void AssemblyFrameworkContractCannotReuseSuccessAfterAmbientInputChanges()
    {
        const string variable = "AFFECTED_FRAMEWORK_INPUT";
        var previous = Environment.GetEnvironmentVariable(variable);
        try
        {
            Environment.SetEnvironmentVariable(variable, "pass");
            using var fixture = new AffectedExecutionFixture();
            fixture.Write("tools/tests/StrataLint.First/Framework.cs", """
                using System;
                using System.Reflection;
                using Xunit.Abstractions;
                using Xunit.Sdk;
                [assembly: First.FrameworkSelection]
                namespace First;
                [AttributeUsage(AttributeTargets.Assembly)]
                [TestFrameworkDiscoverer("First.FrameworkDiscoverer", "StrataLint.First")]
                public sealed class FrameworkSelectionAttribute : Attribute, ITestFrameworkAttribute { }
                public sealed class FrameworkDiscoverer : ITestFrameworkTypeDiscoverer
                {
                    public Type GetTestFrameworkType(IAttributeInfo attribute) => typeof(AmbientFramework);
                }
                public sealed class AmbientFramework : XunitTestFramework
                {
                    public AmbientFramework(IMessageSink sink) : base(sink) { }
                    protected override ITestFrameworkExecutor CreateExecutor(AssemblyName assemblyName)
                    {
                        if (Environment.GetEnvironmentVariable("AFFECTED_FRAMEWORK_INPUT") != "pass")
                            throw new InvalidOperationException("framework ambient input rejected");
                        return base.CreateExecutor(assemblyName);
                    }
                }
                """);
            var build = fixture.Build();
            Assert.Equal(2, fixture.Tests(build).Projects.Sum(project => project.Executed));
            Environment.SetEnvironmentVariable(variable, "fail");
            var incremental = fixture.Tests(build, expectedExit: null);
            fixture.ClearSeed();
            var full = fixture.Tests(build, expectedExit: 1);
            Assert.NotNull(full.Projects[0].Error);
            Assert.NotNull(incremental.Projects[0].Error);
            Assert.DoesNotContain(incremental.Projects[0].Coverage, coverage => coverage.Status == "reused");
            Assert.Equal(0, incremental.Projects[1].Executed);
            Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
            Assert.Equal(incremental.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
            Assert.Equal(1, full.Projects[1].Executed);
        }
        finally { Environment.SetEnvironmentVariable(variable, previous); }
    }

    [Fact]
    public void InheritedFactUsesCompleteNativeExecutionOnEveryRound()
    {
        using var fixture = new AffectedExecutionFixture();
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", """
            namespace First;
            public abstract class BaseCases
            {
                [Xunit.Fact] public void Check() { Xunit.Assert.Equal(7, Shared.Value()); }
            }
            public class ConcreteCases : BaseCases { }
            """);
        var build = fixture.Build();
        var cold = fixture.Tests(build);
        Assert.Equal(2, cold.Projects.Sum(project => project.Executed));
        var warm = fixture.Tests(build);
        Assert.Equal(1, warm.Projects.Sum(project => project.Executed));
        Assert.Equal("executed", Assert.Single(warm.Projects[0].Coverage).Status);
        Assert.Equal("reused", Assert.Single(warm.Projects[1].Coverage).Status);
        var trx = TestResultEvidence.Load(Path.Combine(fixture.Root, warm.Projects[0].Results));
        Assert.Contains("First.ConcreteCases.Check", trx.MethodCounts.Keys);
        Assert.DoesNotContain("First.BaseCases.Check", trx.MethodCounts.Keys);
        CommonExecutionEvidence.ValidateTests(fixture.Root);
        var missingExecution = warm with { Projects = warm.Projects.Select(project => project with { Executed = 0 }).ToArray() };
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.TestsPath, missingExecution);
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
        fixture.ClearSeed();
        var full = fixture.Tests(build);
        Assert.Equal(2, full.Projects.Sum(project => project.Executed));
        Assert.Equal(warm.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
    }

    [Theory]
    [InlineData("[Xunit.Fact] public async System.Threading.Tasks.Task Check() { await System.Threading.Tasks.Task.CompletedTask; }")]
    [InlineData("[Xunit.Theory] [Xunit.InlineData(7)] public void Check(int value) { Xunit.Assert.Equal(7, value); }")]
    [InlineData("[CustomFact] public void Check() { Xunit.Assert.True(true); }")]
    [InlineData("[Xunit.Fact] public void Check() { Xunit.Assert.False(System.Threading.Tasks.Task.Delay(1).IsCanceled); }")]
    public void UnresolvedDiscoveryRunsTheWholeNativeProject(string test)
    {
        using var fixture = new AffectedExecutionFixture();
        if (test.Contains("InlineData", StringComparison.Ordinal)) fixture.UnenrollFirst();
        fixture.Write("tools/tests/StrataLint.First/Additional.cs", "namespace First; public class Additional { " + test
            + " } public sealed class CustomFactAttribute : Xunit.FactAttribute { }");
        var build = fixture.Build();
        Assert.Equal(3, fixture.Tests(build).Projects.Sum(project => project.Executed));
        var warm = fixture.Tests(build);
        Assert.Equal(2, warm.Projects[0].Executed);
        var coverage = Assert.Single(warm.Projects[0].Coverage);
        Assert.Equal("*", coverage.Scope);
        Assert.Equal("executed", coverage.Status);
        Assert.Equal(2, coverage.Covered);
        Assert.Equal(0, warm.Projects[1].Executed);
        CommonExecutionEvidence.ValidateTests(fixture.Root);
        fixture.ClearSeed();
        var full = fixture.Tests(build);
        Assert.Equal(3, full.Projects.Sum(project => project.Executed));
        Assert.Equal(warm.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
    }
}
