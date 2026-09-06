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
    public void LazyNeverBindsUnreachableCallableEdges()
    {
        var fixture = Synthetic("""
            class Cases {
              [Fact] public void Root() => Used();
              static void Used() { }
              static void Unused() => Missing();
            }
            """);
        var (map, eager, lazy) = Compare(fixture);
        AssertReasons(map, "Cases.Root");
        Assert.Contains(eager.Bound, static item => item.Identity.DeclarationId == "M:Cases.Unused");
        AssertBound(lazy, "M:Cases.Root", "M:Cases.Used", "M:Cases.#ctor");
        Assert.All(lazy.Bound, item => {
            Assert.Equal("Tests", item.ProjectPath);
            Assert.Equal("tests/Cases.cs", item.SourcePath);
            Assert.Equal("Tests", item.Identity.AssemblyName);
            Assert.True(item.Span.Length > 0);
        });
    }

    [Fact]
    public void LazyRelevanceMemoizesSharedPositiveAndNegativeSubgraphs()
    {
        var fixture = ProjectFixture("""
            class Cases { [Xunit.Fact] public void Root() { Production.Root(); Production.Negative(); } }
            """, """
            public static class Production {
              public static void Root() { Left(); Right(); }
              static void Left() { Shared(); }
              static void Right() { Shared(); }
              static void Shared() { Seed(); }
              [StrataLint.Engine.CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
              static void Seed() { Missing(); }
              public static void Negative() { NLeft(); NRight(); }
              static void NLeft() { NShared(); }
              static void NRight() { NShared(); }
              static void NShared() { Missing(); }
            }
            """);
        var (map, _, lazy) = Compare(fixture);
        AssertReasons(map, "Cases.Root", TestMapUnknownReason.Other);
        AssertBound(lazy, "M:Cases.Root", "M:Cases.#ctor", "M:Production.Root", "M:Production.Left",
            "M:Production.Right", "M:Production.Shared", "M:Production.Seed", "M:Production.Negative",
            "M:Production.NLeft", "M:Production.NRight", "M:Production.NShared",
            "M:StrataLint.Engine.CompileTimeInputUniverseAttribute.#ctor(System.String,System.String)",
            "M:Xunit.FactAttribute.#ctor");
        Assert.Equal(new[] { "M:Production.Left", "M:Production.Right", "M:Production.Root", "M:Production.Seed", "M:Production.Shared" },
            lazy.Expanded.Select(static item => item.Identity.DeclarationId).Order(StringComparer.Ordinal));
        Assert.All(lazy.Expanded.GroupBy(static item => item), group => Assert.Single(group));
    }

    [Fact]
    public void LazyBindingStateIsIsolatedBetweenDerivations()
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
    public void LazyAndEagerUnknownDebtFindingsAreByteIdentical()
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
        var (map, eager, lazy) = Compare(fixture);
        AssertReasons(map, "Cases.Root", TestMapUnknownReason.VariablePath);
        var constructor = Assert.Single(lazy.Bound, static item => item.Identity.DeclarationId == "M:Cases.#ctor");
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
    public void UnreachableCrossTreeRootInitializerChangesFailureDomain()
    {
        var fixture = ProjectFixture("""
            partial class Cases { [Xunit.Fact] public void Root() { } static void Unused() => Production.Read(root); }
            """, "public static class Production { public static void Read(string path) { } }");
        var project = fixture.Context!.Projects[1];
        fixture = fixture with { Context = fixture.Context with { Projects = [fixture.Context.Projects[0],
            project with { Sources = [.. project.Sources, new("tests/Root.cs", """
                partial class Cases { static string root = FindRoot(); static string FindRoot() => ""; }
                """)] }] } };
        Assert.Throws<ArgumentException>(() => Derive(fixture, ScribeBindingStrategy.Eager));
        var lazy = Derive(fixture, ScribeBindingStrategy.Demand);
        AssertReasons(lazy, "Cases.Root");
        var expected = new ScribeTestMap([new("Tests", "tests/Cases.cs", "Cases.Root", [])], [], [], [], []);
        Assert.Equal(Bytes(expected), Bytes(lazy));
    }

    internal static (ScribeTestMap Map, Recorder Eager, Recorder Lazy) Compare(Fixture fixture)
    {
        var eager = new Recorder();
        var lazy = new Recorder();
        var eagerMap = Derive(fixture, ScribeBindingStrategy.Eager, recorder: eager);
        var lazyMap = Derive(fixture, ScribeBindingStrategy.Demand, recorder: lazy);
        Assert.Equal(Bytes(eagerMap), Bytes(lazyMap));
        Assert.All(lazy.Bound.GroupBy(static item => item), group => Assert.Single(group));
        return (lazyMap, eager, lazy);
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
