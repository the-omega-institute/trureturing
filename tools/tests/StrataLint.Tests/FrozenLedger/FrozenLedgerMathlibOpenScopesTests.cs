using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("open Nat in ", "unchanged", true)]
    [InlineData("open Nat in ", "prefix", false)]
    [InlineData("open Nat in ", "value", false)]
    [InlineData("open Nat in private meta ", "unchanged", true)]
    [InlineData("open Nat in private meta ", "prefix", false)]
    [InlineData("open Nat in private meta ", "value", false)]
    public void MathlibReanchorTracksOpenScopedDeclarationPrefixes(
        string prefix, string mutation, bool authorized)
    {
        var source = "namespace N\n" + prefix + "def seed : Nat := succ 0\nend N\n";
        var root = ModuleWithReport("A", source, "old open scoped definition",
            declarations: ["N.seed"], kind: "def");
        var candidate = root with
        {
            Source = mutation switch
            {
                "prefix" => source.Replace("open Nat", "open Int", StringComparison.Ordinal),
                "value" => source.Replace("succ 0", "succ 1", StringComparison.Ordinal),
                _ => source,
            },
            StatementMaterial = "new open scoped definition",
        };

        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("scoped instance ", "unchanged", true)]
    [InlineData("scoped instance ", "value", false)]
    [InlineData("scoped instance ", "priority", false)]
    [InlineData("scoped instance ", "removed", false)]
    [InlineData("instance ", "unchanged", true)]
    [InlineData("instance ", "value", false)]
    [InlineData("instance ", "priority", false)]
    [InlineData("instance ", "removed", false)]
    [InlineData("instance (priority := 100) ", "unchanged", true)]
    [InlineData("instance (priority := 100) ", "value", false)]
    [InlineData("instance (priority := 100) ", "priority", false)]
    [InlineData("instance (priority := 100) ", "removed", false)]
    public void MathlibReanchorTracksImportedNamedInstanceCommands(
        string prefix, string mutation, bool authorized)
    {
        var declaration = prefix + "box : Box := ⟨7⟩\n";
        var dependency = ModuleWithReport("B", "namespace N\nclass Box where val : Nat\n"
            + declaration + "end N\n", "scoped instance command", declarations: ["N.box"], kind: "def");
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\nopen scoped N\nnamespace M\n"
            + "theorem a : N.Box.val = N.Box.val := rfl\nend M\n", "old scoped instance command use",
            declarations: ["M.a"]) with { Imports = ["B"] };
        var candidateDependency = dependency with
        {
            Source = mutation switch
            {
                "value" => dependency.Source.Replace("⟨7⟩", "⟨8⟩", StringComparison.Ordinal),
                "priority" => dependency.Source.Replace(prefix,
                    prefix.StartsWith("scoped", StringComparison.Ordinal)
                        ? "scoped instance (priority := 50) " : "instance (priority := 50) ",
                    StringComparison.Ordinal),
                "removed" => dependency.Source.Replace(declaration, "", StringComparison.Ordinal),
                _ => dependency.Source,
            },
        };

        var result = ValidateMathlibReanchor([root, dependency],
            [root with { StatementMaterial = "new scoped instance command use" }, candidateDependency],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("scoped instance ", "unchanged", true)]
    [InlineData("scoped instance ", "value", false)]
    [InlineData("scoped instance (priority := 100) ", "unchanged", true)]
    [InlineData("scoped instance (priority := 100) ", "value", false)]
    [InlineData("instance (priority := 100) ", "unchanged", true)]
    [InlineData("instance (priority := 100) ", "value", false)]
    public void MathlibReanchorResolvesNamedInstanceRoots(
        string prefix, string mutation, bool authorized)
    {
        var source = "namespace N\nclass Box where val : Nat\n"
            + prefix + "box : Box := ⟨7⟩\nend N\n";
        var root = ModuleWithReport("A", source, "old scoped instance root",
            declarations: ["N.box"], kind: "def");
        var candidate = root with
        {
            Source = mutation == "value" ? source.Replace("⟨7⟩", "⟨8⟩", StringComparison.Ordinal) : source,
            StatementMaterial = "new scoped instance root",
        };

        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }
}
