using StrataLint.Engine;
using Xunit;

namespace StrataLint.Tests;

public sealed partial class ScribeDemandBindingEquivalenceTests
{
    // Base f45173ac8090 IsRepositoryRoot first asks GetSymbolInfo for every invocation.
    // A string-returning FindRoot matches regardless of callee syntax or method kind.
    // Delegate Invoke and nameof have no FindRoot method symbol; neither expression
    // contains Root.FullPath nor is an identifier with a repository-root initializer.
    // The extra parentheses disambiguate a method group from a cast. The review's
    // single-parenthesized spelling parses as an invalid cast (CS1525/CS0246), so
    // base emits Other for that separate negative row, not IndirectViaProductionLoader.
    [Theory]
    [InlineData("simple", "FindRoot()", "", "IndirectViaProductionLoader")]
    [InlineData("member-access", "Helper.FindRoot()", "", "IndirectViaProductionLoader")]
    [InlineData("member-binding", "h?.FindRoot()", "var h = new InstanceHelper();", "IndirectViaProductionLoader")]
    [InlineData("parenthesized", "((FindRoot))()", "", "IndirectViaProductionLoader")]
    [InlineData("cast-ambiguous", "(FindRoot)()", "", "Other")]
    [InlineData("generic", "FindRoot<int>()", "", "IndirectViaProductionLoader")]
    [InlineData("delegate", "del()", "System.Func<string> del = FindRoot;", null)]
    [InlineData("local-function", "FindRoot()", "string FindRoot() => \"\";", "IndirectViaProductionLoader")]
    [InlineData("nameof", "nameof(FindRoot)", "", null)]
    public void RepositoryRootInvocationShapesAreClassifiedAsBase(
        string shape, string expression, string setup, string? expectedReason)
    {
        var fixture = ProjectFixture($$"""
            class Cases {
              [Xunit.Fact] public void Root() { {{setup}} Production.Read({{expression}}); }
              static string FindRoot() => "";
              static string FindRoot<T>() => "";
            }
            static class Helper { public static string FindRoot() => ""; }
            class InstanceHelper { public string FindRoot() => ""; }
            """, "public static class Production { public static void Read(string path) { } }");
        var expected = new ScribeTestMap([new("Tests", "tests/Cases.cs", "Cases.Root",
            expectedReason is { } reason ? [Enum.Parse<TestMapUnknownReason>(reason)] : [])], [], [], [], []);

        foreach (var strategy in new[] { ScribeBindingStrategy.Eager, ScribeBindingStrategy.Demand })
        {
            var actual = Derive(fixture, strategy);
            Assert.True(Bytes(expected).SequenceEqual(Bytes(actual)),
                $"{shape} ({strategy}): expected {System.Text.Encoding.UTF8.GetString(Bytes(expected))}; "
                + $"actual {System.Text.Encoding.UTF8.GetString(Bytes(actual))}");
        }
    }

    [Fact]
    public void ParenthesizedFindRootInvocationKeepsIndirectProductionLoader()
    {
        var fixture = ProjectFixture("""
            class Cases {
              [Xunit.Fact] public void Root() => Production.Read(((FindRoot))());
              static string FindRoot() => "";
            }
            """, "public static class Production { public static void Read(string path) { } }");
        foreach (var strategy in new[] { ScribeBindingStrategy.Eager, ScribeBindingStrategy.Demand })
            AssertReasons(Derive(fixture, strategy), "Cases.Root", TestMapUnknownReason.IndirectViaProductionLoader);
    }
}
