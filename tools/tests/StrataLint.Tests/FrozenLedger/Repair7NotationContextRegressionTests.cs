using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("FirstOrder")]
    [InlineData("Ordinary")]
    public void Repair7InitOnlyScopeImportAdjacencyRetainsManagedEdge(string ns)
    {
        var helper = TextFile(PathFor("Helper"),
            $"import Init\nnamespace {ns}\ndef g' : Nat := 0\nend {ns}\nopen {ns}\n"
            + "example : ')' =')' := by decide\n");
        var consumer = TextFile(PathFor("A"), "import D5.S0.Carrier.Helper\ntheorem a : True := by trivial\n");
        var adjacency = LeanImportAdjacency.BuildFromSources(Snapshot([helper, consumer]));
        Assert.Equal(RepoPathFor("Helper"), Assert.Single(adjacency[RepoPathFor("A")]));
        Assert.Empty(adjacency[RepoPathFor("Helper")]);
    }

    [Fact]
    public void Repair7CurrentReferenceCapabilityStopsAtExternalModuleFrontier()
    {
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [PathFor("A")] = new(["D5.S0.Carrier.Helper"], []),
            [PathFor("Helper")] = new(["Mathlib.ModelTheory.Semantics"], []),
        });
        Assert.True(LeanImportClosure.ImportsExternalModule(report,
            "D5.S0.Carrier.A", "Mathlib.ModelTheory.Semantics"));
        // This is the existing capability's frontier, not an assertion about Lean's environment.
        // The compiling environment probe finds Syntax transitively through Semantics.
        Assert.False(LeanImportClosure.ImportsExternalModule(report,
            "D5.S0.Carrier.A", "Mathlib.ModelTheory.Syntax"));
    }

    [Theory]
    [InlineData(false, false, "g'")]
    [InlineData(true, false, "g'")]
    [InlineData(false, true, "g'")]
    [InlineData(true, true, "g'")]
    [InlineData(false, false, "a'")]
    [InlineData(true, false, "a'")]
    [InlineData(false, true, "a'")]
    [InlineData(true, true, "a'")]
    public void Repair7IndentedScopeRejectsChangedRealDependency(bool indented, bool spaced, string name)
    {
        var source = FirstOrderEqualitySource(spaced, name)
            .Replace("\nopen scoped", indented ? "\n open scoped" : "\nopen scoped", StringComparison.Ordinal);
        AssertIdentifierReanchor(source, source.Replace(".inl 0", ".inl 1", StringComparison.Ordinal),
            [], [], expected: false);
    }

    [Theory]
    [InlineData("FirstOrder", "proof")]
    [InlineData("Ordinary", "proof")]
    [InlineData("FirstOrder", "unrelated")]
    [InlineData("Ordinary", "unrelated")]
    [InlineData("FirstOrder", "whitespace")]
    [InlineData("Ordinary", "whitespace")]
    [InlineData("FirstOrder", "literal")]
    [InlineData("Ordinary", "literal")]
    public void Repair7InitOnlyScopeReanchorsByCharacterStatement(string ns, string change)
    {
        var before = $"import Init\nnamespace {ns}\ndef g' : Nat := 0\nend {ns}\nopen {ns}\n"
            + "theorem a : 'g' ='g' := by rfl\n";
        var after = change switch
        {
            "proof" => before.Replace("by rfl", "by exact rfl", StringComparison.Ordinal),
            "unrelated" => before.Replace(":= 0", ":= 1", StringComparison.Ordinal),
            "whitespace" => before.Replace("='g'", "= 'g'", StringComparison.Ordinal),
            "literal" => before.Replace("'g'", "'a'", StringComparison.Ordinal),
            _ => throw new ArgumentException(nameof(change)),
        };
        AssertIdentifierReanchor(before, after, [], [], expected: change != "literal");
    }
}
