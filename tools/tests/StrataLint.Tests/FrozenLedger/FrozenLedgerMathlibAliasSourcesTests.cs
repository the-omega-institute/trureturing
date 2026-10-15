using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("theorem", "unchanged", true)]
    [InlineData("theorem", "target", false)]
    [InlineData("theorem", "type", false)]
    [InlineData("theorem", "proof", true)]
    [InlineData("theorem", "unrelated", true)]
    [InlineData("theorem", "removed", false)]
    [InlineData("def", "unchanged", true)]
    [InlineData("def", "target", false)]
    [InlineData("def", "value", false)]
    [InlineData("def", "unrelated", true)]
    [InlineData("def", "removed", false)]
    public void MathlibReanchorTracksPlainAliasTargetSources(string kind, string mutation, bool authorized)
    {
        var target = kind == "theorem" ? "theorem original : True := by trivial\n"
            : "def original : Nat := 7\n";
        var source = "namespace N\n" + target + "def unrelated : Nat := 0\n"
            + "alias renamed := original\nend N\n";
        var root = ModuleWithReport("A", source, "old alias source", declarations: ["N.renamed"], kind: kind);
        var candidate = root with
        {
            Source = mutation switch
            {
                "target" => source.Replace("alias renamed := original", "alias renamed := N.other", StringComparison.Ordinal),
                "type" => source.Replace(": True :=", ": True ∧ True :=", StringComparison.Ordinal),
                "proof" => source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
                "value" => source.Replace(":= 7", ":= 8", StringComparison.Ordinal),
                "unrelated" => source.Replace("unrelated : Nat := 0", "unrelated : Nat := 1", StringComparison.Ordinal),
                "removed" => source.Replace("alias renamed := original\n", "", StringComparison.Ordinal),
                _ => source,
            },
            StatementMaterial = "new alias source",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("unchanged", true)]
    [InlineData("target", false)]
    [InlineData("value", false)]
    public void MathlibReanchorTracksImportedAliasDefinition(string mutation, bool authorized)
    {
        var dependency = ModuleWithReport("B", "namespace N\ndef original : Nat := 7\n"
            + "alias renamed := original\nend N\n", "alias dependency", declarations: ["N.renamed"], kind: "def");
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\ntheorem a : N.renamed = 7 := rfl\n",
            "old alias consumer", declarations: ["a"]) with { Imports = ["B"] };
        var candidateDependency = dependency with
        {
            Source = mutation switch
            {
                "target" => dependency.Source.Replace("renamed := original", "renamed := N.other", StringComparison.Ordinal),
                "value" => dependency.Source.Replace(":= 7", ":= 8", StringComparison.Ordinal),
                _ => dependency.Source,
            },
        };
        var result = ValidateMathlibReanchor([root, dependency],
            [root with { StatementMaterial = "new alias consumer" }, candidateDependency], ["A"],
            ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("alias renamed := original", "opaque")]
    [InlineData("alias ⟨renamed, reverse⟩ := original", "theorem")]
    [InlineData("alias renamed := original 1", "def")]
    public void MathlibReanchorRejectsUnsupportedAliasSource(string command, string kind)
    {
        var root = ModuleWithReport("A", "namespace N\ndef original : Nat := 7\n" + command + "\nend N\n",
            "old unsupported alias", declarations: ["N.renamed"], kind: kind);
        var result = ValidateMathlibReanchor([root, Module("B")],
            [root with { StatementMaterial = "new unsupported alias" }, Module("B")], ["A"],
            ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("partial ", "opaque", "unchanged", true)]
    [InlineData("partial ", "opaque", "value", false)]
    [InlineData("partial ", "opaque", "modifier", false)]
    [InlineData("partial ", "def", "unchanged", false)]
    [InlineData("", "opaque", "unchanged", false)]
    [InlineData("@[partial] ", "opaque", "unchanged", false)]
    public void MathlibReanchorTracksOpaquePartialDefinitions(
        string prefix, string kind, string mutation, bool authorized)
    {
        var source = "namespace N\n" + prefix + "def value : Nat := 7\nend N\n";
        var root = ModuleWithReport("A", source, "old partial definition", declarations: ["N.value"], kind: kind);
        var candidate = root with
        {
            Source = mutation switch
            {
                "value" => source.Replace(":= 7", ":= 8", StringComparison.Ordinal),
                "modifier" => source.Replace("partial ", "", StringComparison.Ordinal),
                _ => source,
            },
            StatementMaterial = "new partial definition",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")], ["A"],
            ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("infix", false)]
    [InlineData("infixl", false)]
    [InlineData("infixr", false)]
    [InlineData("prefix", false)]
    [InlineData("postfix", false)]
    [InlineData("infix", true)]
    [InlineData("infixl", true)]
    [InlineData("infixr", true)]
    [InlineData("prefix", true)]
    [InlineData("postfix", true)]
    public void MathlibReanchorKeepsNotationAfterPlainAlias(string notation, bool changeNotation)
    {
        var source = "namespace N\ndef original (x y : Nat) : Nat := x + y\n"
            + "alias renamed := original\n" + notation + ":90 \"⊞\" => renamed\nend N\n";
        var root = ModuleWithReport("A", source, "old alias notation", declarations: ["N.renamed"], kind: "def");
        var candidate = root with
        {
            Source = changeNotation ? source.Replace(":90", ":91", StringComparison.Ordinal) : source,
            StatementMaterial = "new alias notation",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeNotation, result.Authorized);
    }

    [Theory]
    [InlineData("infix", "1 ⊞ 2")]
    [InlineData("infixl", "1 ⊞ 2")]
    [InlineData("infixr", "1 ⊞ 2")]
    [InlineData("prefix", "⊞ 1")]
    [InlineData("postfix", "1 ⊞")]
    public void MathlibReanchorRejectsNotationOperatorDependencies(string notation, string application)
    {
        var target = notation is "prefix" or "postfix" ? "def original (x : Nat) : Nat := x\n"
            : "def original (x y : Nat) : Nat := x + y\n";
        var source = "namespace N\n" + target + notation + ":90 \"⊞\" => original\n"
            + "theorem consumer : (" + application + ") = 3 := by decide\nend N\n";
        var root = ModuleWithReport("A", source, "old notation consumer", declarations: ["N.consumer"]);
        var result = ValidateMathlibReanchor([root, Module("B")],
            [root with { StatementMaterial = "new notation consumer" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }
}
