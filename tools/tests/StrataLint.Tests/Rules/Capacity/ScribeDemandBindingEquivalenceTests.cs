using System.Text;
using System.Text.Json;
using Microsoft.CodeAnalysis;
using StrataLint.Engine;
using Trureturing.Truth;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.Tests;

public sealed partial class ScribeDemandBindingEquivalenceTests(ITestOutputHelper output)
{
    [Fact]
    public void DemandAndEagerCallableKindsProduceIdenticalMapBytes()
    {
        var fixture = Synthetic("""
            class Cases {
              static string path = "variable";
              [Fact] public void Method() => Read();
              [Fact] public void Getter() { _ = Get; }
              [Fact] public void Setter() { Set = "x"; }
              [Fact] public void Initializer() { _ = new Init { Value = "x" }; }
              [Fact] public void Expression() { _ = Expr; }
              [Fact] public void Automatic() { _ = Auto; }
              [Fact] public void Indexer() { _ = this[0]; }
              [Fact] public void Local() { Used(); void Used() => Read(); void Unused() => Missing(); }
              [Fact] public void Constructor() { _ = new Built(); }
              [Fact] public void Operator() { _ = new Number() + new Number(); }
              static void Read() { _ = File.ReadAllText(path); }
              string Get { get { Read(); return ""; } }
              string Set { get => ""; set { Read(); } }
              string Expr => File.ReadAllText(path);
              string Auto { get; set; }
              string this[int i] { get { Read(); return ""; } set { Read(); } }
              void Unused() => Missing();
              class Init { public string Value { get => ""; init { Read(); } } }
              class Built { public Built() => Read(); }
              class Number { public Number() => Read(); public static Number operator +(Number a, Number b) { Read(); return a; } }
            }
            """);
        var recorder = new ScribeDemandBindingIsolationTests.Recorder();
        var map = EqualMaps(fixture, demandRecorder: recorder);
        AssertReasons(map, "Cases.Automatic");
        foreach (var name in new[] { "Method", "Getter", "Setter", "Initializer", "Expression", "Indexer", "Local", "Constructor", "Operator" })
            AssertReasons(map, "Cases." + name, TestMapUnknownReason.VariablePath);
        AssertBoundKeys(fixture, recorder,
            "M:Cases.#ctor",
            "M:Cases.Automatic",
            "M:Cases.Built.#ctor",
            "M:Cases.Constructor",
            "M:Cases.Expression",
            "M:Cases.Getter",
            "M:Cases.Indexer",
            "M:Cases.Init.#ctor",
            "M:Cases.Init.get_Value~System.String",
            "M:Cases.Init.set_Value(System.String)",
            "M:Cases.Initializer",
            "M:Cases.Local",
            "M:Cases.Method",
            "M:Cases.Number.#ctor",
            "M:Cases.Operator",
            "M:Cases.Read",
            "M:Cases.Setter",
            "M:Cases.get_Auto~System.String",
            "M:Cases.get_Expr~System.String",
            "M:Cases.get_Get~System.String",
            "M:Cases.get_Item(System.Int32)~System.String",
            "M:Cases.get_Set~System.String",
            "M:Cases.set_Auto(System.String)",
            "M:Cases.set_Item(System.Int32,System.String)",
            "M:Cases.set_Set(System.String)",
            "LocalFunction:void Used() => Read();");
    }

    [Fact]
    public void DemandAndEagerTestAndFixtureConstructorsProduceIdenticalMapBytes()
    {
        var map = EqualMaps(Synthetic("""
            class Cases : IClassFixture<Fixture> {
              public Cases() { }
              public Cases(int unused) { }
              [Fact] public void Empty() { }
            }
            class Fixture {
              public Fixture() { }
              public Fixture(int unused) { _ = File.ReadAllText(Input()); }
              static string Input() => "variable";
            }
            """));
        AssertReasons(map, "Cases.Empty", TestMapUnknownReason.VariablePath);
    }

    [Fact]
    public void DemandAndEagerImplicitConstructorsProduceIdenticalMapBytes()
    {
        var map = EqualMaps(ProjectFixture("""
            class Cases {
              string field = File.ReadAllText(Input());
              string Property { get; } = File.ReadAllText(Input());
              static string Input() => "variable";
              [Xunit.Fact] public void Empty() { _ = DocumentAssembly.Value; }
            }
            """, """
            public static class DocumentAssembly {
              static string data = Discover();
              public static string Value => data;
              [StrataLint.Engine.CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
              static string Discover() { Missing(); return ""; }
            }
            """));
        AssertReasons(map, "Cases.Empty", TestMapUnknownReason.VariablePath, TestMapUnknownReason.Other);
    }

    [Fact]
    public void DemandAndEagerPartialMethodsPreserveBodySelectionAndMultiplicity()
    {
        var fixture = Synthetic("""
            partial class Cases { [Fact] public partial void Check(); }
            """, """
            partial class Cases { [Fact] public partial void Check() { _ = File.ReadAllText(Input()); }
              static string Input() => "variable";
            }
            """);
        var map = EqualMaps(fixture);
        Assert.Equal(2, map.Methods.Count);
        Assert.Equal(new[] { "Cases.Check", "Cases.Check" }, map.Methods.Select(static method => method.Id));
        Assert.Equal(new[] { 0, 1 }, map.Methods.Select(static method => method.UnknownReasons.Count));
    }

    [Fact]
    public void DemandAndEagerProductionRelevanceCyclesProduceIdenticalMapBytes()
    {
        var map = EqualMaps(ProjectFixture("""
            class Cases {
              [Xunit.Fact] public void Positive() => Production.A();
              [Xunit.Fact] public void Negative() => Production.X();
              [Xunit.Fact] public void Bridge() => Production.Bridge();
            }
            """, """
            public static class Production {
              public static void A() { B(); }
              public static void B() { A(); Seed(); }
              [StrataLint.Engine.CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
              static void Seed() { Missing(); }
              public static void X() { Y(); Missing(); }
              public static void Y() { X(); }
              public static void Bridge() { Middle.Hop(); Missing(); }
            }
            """, """
            public static class Middle {
              public static void Hop() { Seed(); }
              [StrataLint.Engine.CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
              static void Seed() { Missing(); }
            }
            """));
        AssertReasons(map, "Cases.Positive", TestMapUnknownReason.Other);
        AssertReasons(map, "Cases.Negative");
        AssertReasons(map, "Cases.Bridge");
    }

    [Fact]
    public void DemandAndEagerMetadataDegradationProduceIdenticalMapBytes()
    {
        var fixture = ProjectFixture("""
            class Cases {
              [Xunit.Fact] public void Empty() { }
              [Xunit.Fact] public void Broken() { Missing(); }
            }
            """, "public static class Production { }");
        var project = fixture.Context!.Projects[1];
        fixture = fixture with { Context = fixture.Context with { Projects = [
            fixture.Context.Projects[0],
            project with {
                ProjectContent = "<Project><ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>",
                Sources = [new("tests/Cases.cs", fixture.Sources[0].Content)],
                PackageLockContent = """
                    {"dependencies":{"net10.0":{"xunit.extensibility.core":{"resolved":"0.0.0-l4-missing"},"xunit.assert":{"resolved":"0.0.0-l4-missing"}}}}
                    """
            }
        ] } };
        var map = EqualMaps(fixture);
        AssertReasons(map, "Cases.Empty", TestMapUnknownReason.MetadataUnavailable);
        AssertReasons(map, "Cases.Broken", TestMapUnknownReason.MetadataUnavailable, TestMapUnknownReason.Other);
    }

    [Fact]
    public void DemandAndEagerReachableDocumentsProduceIdenticalMapBytes()
    {
        var fixture = Documents();
        var recorder = new ScribeDemandBindingIsolationTests.Recorder();
        var map = EqualMaps(fixture, demandRecorder: recorder);
        AssertReasons(map, "Cases.Read", TestMapUnknownReason.Other);
        ScribeDemandBindingIsolationTests.AssertBound(recorder,
            "M:Cases.#ctor",
            "M:Cases.Read",
            "M:DocumentAssembly.#cctor",
            "M:DocumentAssembly.Discover~System.String",
            "M:DocumentAssembly.get_Definitions~System.String",
            "M:DocumentAssembly.get_Value~System.String",
            "M:StrataLint.Engine.CompileTimeInputUniverseAttribute.#ctor(System.String,System.String)",
            "M:Xunit.FactAttribute.#ctor");
        Assert.DoesNotContain(recorder.Bound,
            static item => item.Identity.DeclarationId == "M:DocumentAssembly.Unrelated");
    }

    [Fact]
    public void EmptyDegradedTestsRetainDiscoveryAndMetadataReason()
    {
        var fixture = ProjectFixture("""
            enum RepositoryRootCriterion { Known }
            readonly record struct RepositoryRoot(string FullPath);
            sealed class RepositoryAccessor {
              public RepositoryRoot Root { get; } = new("");
              public static RepositoryAccessor Discover(RepositoryRootCriterion criterion) => new();
            }
            class Cases {
              [Xunit.Fact] public void Empty() { }
              [Xunit.Fact] public void Known() { _ = RepositoryAccessor.Discover(RepositoryRootCriterion.Known); }
              static void Unused() => Missing();
            }
            class Uncalled {
              bool Matches(RepositoryRootCriterion criterion, string root) => criterion switch {
                RepositoryRootCriterion.Known => File.Exists(Path.Combine(root, "marker")),
                _ => false
              };
            }
            """, "public static class Production { }");
        var project = fixture.Context!.Projects[1];
        fixture = fixture with { Context = fixture.Context with { Projects = [
            fixture.Context.Projects[0],
            project with {
                ProjectContent = "<Project><ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>",
                Sources = [new("tests/Cases.cs", fixture.Sources[0].Content)],
                PackageLockContent = """
                    {"dependencies":{"net10.0":{"xunit.extensibility.core":{"resolved":"0.0.0-l4-missing"},"xunit.assert":{"resolved":"0.0.0-l4-missing"}}}}
                    """
            }
        ] } };
        var recorder = new ScribeDemandBindingIsolationTests.Recorder();
        var map = EqualMaps(fixture, demandRecorder: recorder);
        AssertReasons(map, "Cases.Empty", TestMapUnknownReason.MetadataUnavailable);
        AssertReasons(map, "Cases.Known", TestMapUnknownReason.MetadataUnavailable);
        Assert.DoesNotContain(recorder.Bound,
            static item => item.Identity.DeclarationId == "M:Cases.Unused");
    }

    [Fact]
    public void DemandAndEagerPreserveDiscoveryAndAllAuxiliaryMapFields()
    {
        var fixture = Synthetic("""
            class Cases { [Fact] public void Read() { _ = RepositoryAccessor.Discover(RepositoryRootCriterion.Known); } }
            enum RepositoryRootCriterion { Known }
            """, """
            class Uncalled {
              bool Matches(RepositoryRootCriterion criterion, string root) => criterion switch {
                RepositoryRootCriterion.Known => File.Exists(Path.Combine(root, "marker")),
                _ => false
              };
            }
            """);
        var map = EqualMaps(fixture, auxiliary: true);
        AssertReasons(map, "Cases.Read");
        Assert.Equal(new[] { "z.csproj", "a.csproj" }, map.UnclassifiedManagedProjectPaths);
        Assert.Equal(new[] { "z.cs", "a.cs" }, map.OrphanManagedSourcePaths);
        Assert.Equal(new[] { "proof-z", "proof-a" }, map.DanglingCompileFailProofProjectExemptionPaths);
        Assert.Equal(new[] { new MsBuildCompileFinding("z", "message z"), new("a", "message a") }, map.CompileQueryFindings);
    }

    private ScribeTestMap EqualMaps(
        Fixture fixture,
        bool auxiliary = false,
        ScribeDemandBindingIsolationTests.Recorder? demandRecorder = null)
    {
        var eager = Derive(fixture, ScribeBindingStrategy.Eager, auxiliary);
        var demand = Derive(fixture, ScribeBindingStrategy.Demand, auxiliary, demandRecorder);
        Assert.Equal(Bytes(eager), Bytes(demand));
        output.WriteLine(Encoding.UTF8.GetString(Bytes(eager)));
        return demand;
    }

    private static void AssertBoundKeys(
        Fixture fixture,
        ScribeDemandBindingIsolationTests.Recorder recorder,
        params string[] expected)
    {
        string Key(ScribeBindingEvent item)
        {
            if (item.Kind != MethodKind.LocalFunction)
            {
                return item.Identity.DeclarationId;
            }

            var source = Assert.Single(fixture.Sources,
                candidate => candidate.Path == item.SourcePath);
            var declaration = source.Content.Substring(item.Span.Start, item.Span.Length);
            return $"{item.Kind}:{declaration}";
        }

        Assert.Equal(expected.Order(StringComparer.Ordinal), recorder.Bound.Select(Key).Order(StringComparer.Ordinal));
    }

    internal static ScribeTestMap Derive(Fixture fixture, ScribeBindingStrategy strategy,
        bool auxiliary = false, IScribeBindingRecorder? recorder = null) =>
        ScribeTestMapDeriver.DeriveSources(
            fixture.Sources, [],
            auxiliary ? ["z.csproj", "a.csproj"] : [],
            auxiliary ? ["z.cs", "a.cs"] : [],
            auxiliary ? ["proof-z", "proof-a"] : [],
            auxiliary ? [new("z", "message z"), new("a", "message a")] : [],
            fixture.Production, fixture.Context, strategy, recorder);

    internal static byte[] Bytes(ScribeTestMap map)
    {
        var envelope = new ScribeTestMapEnvelope(1, new string('a', 64), new string('b', 64),
            new ScribeTestMapProducer(new string('0', 32)),
            new ScribeTestMapEnvironment("fixture", "net10.0", "dotnet", "fixture", "fixture"), map);
        using var document = JsonDocument.Parse(envelope.Write());
        return StructuredCanonicalWriter.WriteJson(document.RootElement.GetProperty("map")).ToArray();
    }

    internal static void AssertReasons(ScribeTestMap map, string id, params TestMapUnknownReason[] reasons) =>
        Assert.Equal(reasons, Assert.Single(map.Methods, method => method.Id == id).UnknownReasons);

    internal sealed record Fixture(TestMapSource[] Sources, IReadOnlySet<string>? Production = null,
        ScribeProjectCompilationContext? Context = null);

    internal static Fixture Synthetic(params string[] sources) => new(sources.Select((source, index) =>
        new TestMapSource(index == 0 ? "tests/Cases.cs" : "tests/Helpers.cs", source, "Tests")).ToArray());

    internal static Fixture Documents() => ProjectFixture("""
        class Cases { [Xunit.Fact] public void Read() { _ = DocumentAssembly.Value; } }
        """, """
        public static class DocumentAssembly {
          static DocumentAssembly() { _ = Definitions; }
          public static string Value => Definitions;
          public static string Definitions => Discover();
          [StrataLint.Engine.CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
          static string Discover() { Missing(); return ""; }
          public static void Unrelated() { Missing(); }
        }
        """);

    internal static Fixture ProjectFixture(string tests, string production, string? middle = null)
    {
        const string attribute = "namespace " + """
            StrataLint.Engine {
              [System.AttributeUsage(System.AttributeTargets.All)]
              public sealed class CompileTimeInputUniverseAttribute : System.Attribute {
                public CompileTimeInputUniverseAttribute(string prefix, string suffix) { }
              }
            }
            """;
        const string xunit = "namespace " + """
            Xunit {
              public class FactAttribute : System.Attribute { }
              public interface IClassFixture<TFixture> { }
            }
            """;
        var documents = new ScribeCompilationProject("src/Documents/Documents.csproj", "<Project />", "Documents",
            middle is null ? [] : ["src/Middle/Middle.csproj"],
            [new("src/Documents/DocumentAssembly.cs", production), new("src/Documents/Attribute.cs", attribute)], null);
        var testProject = new ScribeCompilationProject("tests/Tests.csproj", "<Project />", "Tests",
            [documents.Path], [new("tests/Cases.cs", tests), new("tests/Xunit.cs", xunit)], null);
        ScribeCompilationProject[] projects = middle is null ? [documents, testProject] : [
            documents, testProject, new("src/Middle/Middle.csproj", "<Project />", "Middle", [],
                [new("src/Middle/Middle.cs", middle), new("src/Middle/Attribute.cs", attribute)], null)];
        IReadOnlySet<string> productionAssemblies = new HashSet<string>(StringComparer.Ordinal) { "Documents" };
        return new([new("tests/Cases.cs", tests, "Tests")], productionAssemblies,
            new(projects, productionAssemblies));
    }
}
