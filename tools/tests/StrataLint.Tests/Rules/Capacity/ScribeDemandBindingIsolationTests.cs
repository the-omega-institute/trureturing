using System.Text.Json;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Engine;
using Trureturing.Truth;
using Xunit;
using static StrataLint.Tests.ScribeDemandBindingEquivalenceTests;

namespace StrataLint.Tests;

public sealed class ScribeDemandBindingIsolationTests
{
    [Fact]
    public void DemandNeverBindsUnreachableCallableEdges()
    {
        var fixture = Synthetic("""
            class Cases {
              [Fact] public void Root() => Used();
              static void Used() { }
              static void Unused() => Missing();
            }
            """);
        var (map, eager, demand) = Compare(fixture);
        AssertReasons(map, "Cases.Root");
        Assert.Contains(eager.Bound, static item => item.Identity.DeclarationId == "M:Cases.Unused");
        AssertBound(demand, "M:Cases.Root", "M:Cases.Used", "M:Cases.#ctor");
        Assert.All(demand.Bound, item => {
            Assert.Equal("Tests", item.ProjectPath);
            Assert.Equal("tests/Cases.cs", item.SourcePath);
            Assert.Equal("Tests", item.Identity.AssemblyName);
            Assert.True(item.Span.Length > 0);
        });
    }

    [Fact]
    public void DemandRelevanceMemoizesSharedPositiveAndNegativeSubgraphs()
    {
        var fixture = ProjectFixture("""
            class Cases { [Xunit.Fact] public void Root() { Production.Root(); Production.Negative(); } }
            """, """
            public static class Production {
              public static void Root() { Left(); Right(); }
              static void Left() { Shared(); }
              static void Right() { Shared(); }
              static void Shared() { Seed(); }
              static void Seed() { _ = nameof(Universe); Missing(); }
              [StrataLint.Engine.CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
              static string Universe => "";
              public static void Negative() { NLeft(); NRight(); }
              static void NLeft() { NShared(); }
              static void NRight() { NShared(); }
              static void NShared() { Missing(); }
            }
            """);
        var (map, _, demand) = Compare(fixture);
        AssertReasons(map, "Cases.Root", TestMapUnknownReason.Other);
        AssertBound(demand, "M:Cases.Root", "M:Cases.#ctor", "M:Production.Root", "M:Production.Left",
            "M:Production.Right", "M:Production.Shared", "M:Production.Seed", "M:Production.Negative",
            "M:Production.NLeft", "M:Production.NRight", "M:Production.NShared",
            "M:Xunit.FactAttribute.#ctor");
        Assert.Equal(new[] { "M:Production.Left", "M:Production.Right", "M:Production.Root", "M:Production.Seed", "M:Production.Shared" },
            demand.Expanded.Select(static item => item.Identity.DeclarationId).Order(StringComparer.Ordinal));
        Assert.All(demand.Expanded.GroupBy(static item => item), group => Assert.Single(group));
    }

    [Fact]
    public void DemandBindingStateIsIsolatedBetweenDerivations()
    {
        var fixture = Synthetic("class Cases { [Fact] public void Root() => Missing(); void Unused() { } }");
        var (first, _, firstRecorder) = Compare(fixture);
        var (second, _, secondRecorder) = Compare(fixture);
        Assert.Equal(Bytes(first), Bytes(second));
        Assert.NotSame(firstRecorder, secondRecorder);
        Assert.Equal(firstRecorder.Bound, secondRecorder.Bound);
        AssertBound(firstRecorder, "M:Cases.Root", "M:Cases.#ctor");
        AssertBound(secondRecorder, "M:Cases.Root", "M:Cases.#ctor");
        AssertReasons(second, "Cases.Root", TestMapUnknownReason.Other);
    }

    [Fact]
    public void DemandAndEagerUnknownDebtFindingsAreByteIdentical()
    {
        var fixture = Synthetic("class Cases { [Fact] public void Root() => Missing(); }");
        var current = new[] { Derive(fixture, ScribeBindingStrategy.Eager), Derive(fixture, ScribeBindingStrategy.Demand) };
        var baseline = new[] { Derive(Synthetic("class Cases { [Fact] public void Root() { } }"), ScribeBindingStrategy.Eager),
            Derive(Synthetic("class Cases { [Fact] public void Root() { } }"), ScribeBindingStrategy.Demand) };
        var empty = new[] { Derive(Synthetic("class Unused { }"), ScribeBindingStrategy.Eager),
            Derive(Synthetic("class Unused { }"), ScribeBindingStrategy.Demand) };
        Assert.Equal(Bytes(current[0]), Bytes(current[1]));
        Assert.Equal(Bytes(baseline[0]), Bytes(baseline[1]));
        Assert.Equal(Bytes(empty[0]), Bytes(empty[1]));
        var expectedBlock = FindingBytes([new("tests/Cases.cs",
            "conservative unknown test method introduced after protected baseline: Tests::Cases.Root", AdmissionEffect.Block)]);
        foreach (var now in current)
        foreach (var index in new[] { 0, 1 })
        {
            Assert.Equal(FindingBytes([]), FindingBytes(ScribeUnknownDebtPolicy.Evaluate(now, baseline[index])));
            Assert.Equal(expectedBlock, FindingBytes(ScribeUnknownDebtPolicy.Evaluate(now, empty[index])));
        }
    }

    [Fact]
    public void CanonicalRepresentativeFollowsEagerOccurrenceOrder()
    {
        var fixture = new Fixture([
            new("tests/b.cs", "partial class Cases { string value = File.ReadAllText(Input()); static string Input() => \"v\"; }", "Tests"),
            new("tests/a.cs", "partial class Cases { [Fact] public void Root() { } }", "Tests")]);
        var (map, eager, demand) = Compare(fixture);
        AssertReasons(map, "Cases.Root", TestMapUnknownReason.VariablePath);
        var constructor = Assert.Single(demand.Bound, static item => item.Identity.DeclarationId == "M:Cases.#ctor");
        Assert.Equal("tests/b.cs", constructor.SourcePath);
        Assert.Equal(0, constructor.Span.Start);
        Assert.Equal(fixture.Sources[0].Content.Length, constructor.Span.Length);
        Assert.Equal(Assert.Single(eager.Bound, static item => item.Identity.DeclarationId == "M:Cases.#ctor"), constructor);
    }

    [Fact]
    public void SymbolHitPrecedesEarlierIdentityFallback()
    {
        var fixture = Synthetic("class Cases { [Fact] public void Root() { } }");
        Compare(fixture);
        var first = ScribeTestSymbolBinder.Bind(fixture.Sources, ScribeBindingStrategy.Eager).Single().Callables;
        var second = ScribeTestSymbolBinder.Bind(fixture.Sources, ScribeBindingStrategy.Demand).Single().Callables;
        var index = new ScribeCallableIndex();
        var earlier = Assert.Single(first, static callable => callable.IsTest);
        var later = Assert.Single(second, static callable => callable.IsTest);
        var earlierSymbol = Assert.IsAssignableFrom<IMethodSymbol>(earlier.SemanticModel.GetDeclaredSymbol(earlier.Syntax));
        var laterSymbol = Assert.IsAssignableFrom<IMethodSymbol>(later.SemanticModel.GetDeclaredSymbol(later.Syntax));
        index.Add(earlierSymbol, earlier);
        index.Add(laterSymbol, later);
        Assert.True(index.TryGetValue(laterSymbol, out var selected));
        Assert.Same(later, selected);
        var third = ScribeTestSymbolBinder.Bind(fixture.Sources, ScribeBindingStrategy.Eager).Single().Callables.Single(static callable => callable.IsTest);
        var fallbackSymbol = Assert.IsAssignableFrom<IMethodSymbol>(third.SemanticModel.GetDeclaredSymbol(third.Syntax));
        Assert.True(index.TryGetValue(fallbackSymbol, out selected));
        Assert.Same(earlier, selected);
    }

    [Fact]
    public void UniverseAccumulationDoesNotEraseEarlierOther()
    {
        var fixture = ProjectFixture("""
            class Cases { [Xunit.Fact] public void Root() => Production.Read(); }
            """, """
            public static class Production {
              public static void Read() { _ = System.Activator.CreateInstance(typeof(object)); Seed(); }
              [StrataLint.Engine.CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
              static void Seed() { }
            }
            """);
        var (map, _, _) = Compare(fixture);
        AssertReasons(map, "Cases.Root", TestMapUnknownReason.Other);
    }

    [Fact]
    public void CrossTreeRootInitializerIsClassifiedIdenticallyByEagerAndDemand()
    {
        var fixture = ProjectFixture("""
            partial class Cases { [Xunit.Fact] public void Root() { } static void Unused() => Production.Read(root); }
            """, "public static class Production { public static void Read(string path) { } }");
        var project = fixture.Context!.Projects[1];
        fixture = fixture with { Context = fixture.Context with { Projects = [fixture.Context.Projects[0],
            project with { Sources = [.. project.Sources, new("tests/Root.cs", """
                partial class Cases { static string root = FindRoot(); static string FindRoot() => ""; }
                """)] }] } };
        var expected = new ScribeTestMap([new("Tests", "tests/Cases.cs", "Cases.Root", [])], [], [], [], []);
        var eager = Derive(fixture, ScribeBindingStrategy.Eager);
        var demand = Derive(fixture, ScribeBindingStrategy.Demand);
        Assert.Equal(Bytes(expected), Bytes(eager));
        Assert.Equal(Bytes(expected), Bytes(demand));
        Assert.Equal(Bytes(eager), Bytes(demand));
    }

    [Fact]
    public void ReachableCrossTreeRootInitializerIsClassifiedIdenticallyByEagerAndDemand()
    {
        var fixture = ProjectFixture("""
            partial class Cases { [Xunit.Fact] public void Root() => Production.Read(RootPath); }
            """, "public static class Production { public static void Read(string path) { } }");
        var project = fixture.Context!.Projects[1];
        fixture = fixture with { Context = fixture.Context with { Projects = [fixture.Context.Projects[0],
            project with { Sources = [.. project.Sources, new("tests/Root.cs", """
                partial class Cases { static string RootPath { get; } = FindRoot(); static string FindRoot() => ""; }
                """)] }] } };
        var expected = new ScribeTestMap([new("Tests", "tests/Cases.cs", "Cases.Root",
            [TestMapUnknownReason.IndirectViaProductionLoader])], [], [], [], []);
        var eager = Derive(fixture, ScribeBindingStrategy.Eager);
        var demand = Derive(fixture, ScribeBindingStrategy.Demand);
        Assert.Equal(Bytes(expected), Bytes(eager));
        Assert.Equal(Bytes(expected), Bytes(demand));
        Assert.Equal(Bytes(eager), Bytes(demand));
    }

    [Fact]
    public void CrossTreeSyntacticRootInitializerStaysKnownOnBothStrategies()
    {
        var fixture = ProjectFixture("""
            partial class Cases {
              [Xunit.Fact]
              public void Read() => _ = File.ReadAllText(Path.Combine(root, "marker"));
            }
            """, "public static class Production { }");
        var project = fixture.Context!.Projects[1];
        var sourceA = new ScribeTrackedSource("tests/A.cs", fixture.Sources[0].Content);
        fixture = fixture with
        {
            Sources = [new("tests/A.cs", sourceA.Content, "Tests")],
            Context = fixture.Context with
            {
                Projects =
                [
                    fixture.Context.Projects[0],
                    project with
                    {
                        Sources =
                        [
                            sourceA,
                            project.Sources[1],
                            new("tests/B.cs", """
                                partial class Cases {
                                  static readonly Holder holder = new();
                                  static readonly string root = holder.Root.FullPath;
                                }
                                readonly record struct RepositoryRoot(string FullPath);
                                sealed class Holder { public RepositoryRoot Root { get; } = new(""); }
                                """)
                        ]
                    }
                ]
            }
        };

        var expected = new ScribeTestMap(
            [new("Tests", "tests/A.cs", "Cases.Read", [])], [], [], [], []);
        var eager = Derive(fixture, ScribeBindingStrategy.Eager);
        var demand = Derive(fixture, ScribeBindingStrategy.Demand);

        Assert.DoesNotContain(TestMapUnknownReason.VariablePath,
            Assert.Single(eager.Methods).UnknownReasons);
        Assert.DoesNotContain(TestMapUnknownReason.VariablePath,
            Assert.Single(demand.Methods).UnknownReasons);
        Assert.Equal(Bytes(expected), Bytes(eager));
        Assert.Equal(Bytes(expected), Bytes(demand));
        var noFindings = FindingBytes([]);
        Assert.Equal(noFindings, FindingBytes(ScribeUnknownDebtPolicy.Evaluate(eager, demand)));
        Assert.Equal(noFindings, FindingBytes(ScribeUnknownDebtPolicy.Evaluate(demand, eager)));
    }

    [Fact]
    public void NullRecorderPathAllocatesNoObservationState()
    {
        var fixture = Synthetic("static class Cases { [Fact] public static void Root() { } }");
        var callable = Assert.Single(ScribeTestSymbolBinder.Bind(
            fixture.Sources, ScribeBindingStrategy.Eager).Single().Callables);
        var symbol = Assert.IsAssignableFrom<IMethodSymbol>(
            callable.SemanticModel.GetDeclaredSymbol(callable.Syntax));
        var session = new ScribeDemandBindingSession(
            [callable],
            new Dictionary<ScribeBoundCallable, IMethodSymbol> { [callable] = symbol },
            null,
            static (_, _) => { },
            null);

        Assert.Null(session.ObservationState);
        session.Bind();
    }

    [Fact]
    public void BindNullRecorderCreatesNoObservationState()
    {
        var fixture = Synthetic("static class Cases { }");
        var observed = new List<ScribeBindingObservation?>();

        _ = ScribeTestSymbolBinder.Bind(
            fixture.Sources,
            ScribeBindingStrategy.Demand,
            recorder: null,
            observationStateObserver: observed.Add);

        Assert.Null(Assert.Single(observed));
    }

    internal static (ScribeTestMap Map, Recorder Eager, Recorder Demand) Compare(Fixture fixture)
    {
        var eager = new Recorder();
        var demand = new Recorder();
        var eagerMap = Derive(fixture, ScribeBindingStrategy.Eager, recorder: eager);
        var demandMap = Derive(fixture, ScribeBindingStrategy.Demand, recorder: demand);
        Assert.Equal(Bytes(eagerMap), Bytes(demandMap));
        Assert.All(demand.Bound.GroupBy(static item => item), group => Assert.Single(group));
        return (demandMap, eager, demand);
    }

    internal static void AssertBound(Recorder recorder, params string[] expected) =>
        Assert.Equal(expected.Order(StringComparer.Ordinal),
            recorder.Bound.Select(static item => item.Identity.DeclarationId).Order(StringComparer.Ordinal));

    private static byte[] FindingBytes(IEnumerable<ScribeUnknownDebtFinding> findings) =>
        StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(findings.Select(static finding => new {
            path = finding.Path, message = finding.Message, effect = finding.Effect.ToString()
        }))).ToArray();

    internal sealed class Recorder : IScribeBindingRecorder
    {
        internal List<ScribeBindingEvent> Bound { get; } = [];
        internal List<ScribeBindingEvent> Expanded { get; } = [];
        public void BindingEdges(ScribeBindingEvent callable) => Bound.Add(callable);
        public void ExpandingRelevance(ScribeBindingEvent callable) => Expanded.Add(callable);
    }
}
