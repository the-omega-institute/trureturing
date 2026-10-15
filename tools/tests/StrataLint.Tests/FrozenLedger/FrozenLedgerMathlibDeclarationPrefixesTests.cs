using System.Collections.Immutable;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("omit [Inhabited Nat] in ", "unchanged", true)]
    [InlineData("omit [Inhabited Nat] in ", "prefix", false)]
    [InlineData("omit [Inhabited Nat] in ", "statement", false)]
    [InlineData("include h in ", "unchanged", true)]
    [InlineData("include h in ", "prefix", false)]
    [InlineData("include h in ", "statement", false)]
    public void MathlibReanchorScopedDeclarationPrefixesTrackTheirSource(
        string prefix, string mutation, bool authorized)
    {
        var source = "namespace N\nvariable (h k : Nat)\n" + prefix
            + "theorem a : True := by trivial\nend N\n";
        var root = ModuleWithReport("A", source, "old scoped declaration", declarations: ["N.a"]);
        var candidate = root with
        {
            Source = mutation switch
            {
                "prefix" => source.Replace("Inhabited Nat", "Inhabited Bool", StringComparison.Ordinal)
                    .Replace("include h", "include k", StringComparison.Ordinal),
                "statement" => source.Replace(": True", ": False", StringComparison.Ordinal),
                _ => source,
            },
            StatementMaterial = "new scoped declaration",
        };

        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("@[instance] ", true)]
    [InlineData("@[instance] ", false)]
    [InlineData("@[instance, instance_reducible] ", true)]
    [InlineData("@[instance, instance_reducible] ", false)]
    [InlineData("@[simp, reducible] ", true)]
    [InlineData("@[simp, reducible] ", false)]
    public void MathlibReanchorAttributeKeywordsDoNotReplaceTheDeclarationKind(
        string attributes, bool unchanged)
    {
        var source = "namespace N\n" + attributes + "def seed : Nat := 7\nend N\n";
        var root = ModuleWithReport("A", source, "old attributed definition",
            declarations: ["N.seed"], kind: "def");
        var candidate = root with
        {
            Source = unchanged ? source : source.Replace(":= 7", ":= 8", StringComparison.Ordinal),
            StatementMaterial = "new attributed definition",
        };

        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(unchanged, result.Authorized);
    }

    [Theory]
    [InlineData("N.instance_reducible")]
    [InlineData("N.instance")]
    public void MathlibReanchorAttributesCannotSupplyFabricatedDeclarationRoots(string name)
    {
        const string source = "namespace N\n@[instance, instance_reducible] def seed : Nat := 7\nend N\n";
        var root = ModuleWithReport("A", source, "old fabricated attribute root",
            declarations: [name], kind: "def");

        var result = ValidateMathlibReanchor([root, Module("B")],
            [root with { StatementMaterial = "new fabricated attribute root" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("def seed : Nat := 7\n", "N.instInhabitedNat", false)]
    [InlineData("instance : Inhabited Nat := ⟨0⟩\n", "N.instInhabitedNat", true)]
    [InlineData("inductive S | value deriving Inhabited\n", "N.instInhabitedS", true)]
    public void MathlibReanchorUnboundInstanceNamesRequireASourceGenerator(
        string declarations, string name, bool authorized)
    {
        var source = "namespace N\n" + declarations + "theorem a : True := by trivial\nend N\n";
        var root = ModuleWithReport("A", source, "old instance source",
            declarations: [name], kind: "def");

        var result = ValidateMathlibReanchor([root, Module("B")],
            [root with { StatementMaterial = "new instance source" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("@[instance] ", "unchanged", true)]
    [InlineData("@[instance] ", "value", false)]
    [InlineData("@[instance] ", "priority", false)]
    [InlineData("@[instance] ", "removed", false)]
    [InlineData("@[instance, instance_reducible] ", "value", false)]
    [InlineData("@[instance 100] ", "value", false)]
    [InlineData("@[instance]\n", "unchanged", true)]
    [InlineData("@[instance]\n", "value", false)]
    public void MathlibReanchorTracksImportedAttributedInstanceDefinitions(
        string attribute, string mutation, bool authorized)
    {
        var dependency = ModuleWithReport("B", "namespace N\nclass Box where val : Nat\n"
            + attribute + "def box : Box := ⟨7⟩\nend N\n", "instance source",
            declarations: ["N.box"], kind: "def");
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\nnamespace N\n"
            + "theorem a : Box.val = Box.val := rfl\nend N\n", "old implicit instance use",
            declarations: ["N.a"]) with { Imports = ["B"] };
        var candidateDependency = dependency with
        {
            Source = mutation switch
            {
                "value" => dependency.Source.Replace("⟨7⟩", "⟨8⟩", StringComparison.Ordinal),
                "priority" => dependency.Source.Replace(attribute, "@[instance 50] ", StringComparison.Ordinal),
                "removed" => dependency.Source.Replace(attribute, "", StringComparison.Ordinal),
                _ => dependency.Source,
            },
        };

        var result = ValidateMathlibReanchor([root, dependency],
            [root with { StatementMaterial = "new implicit instance use" }, candidateDependency],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("unchanged", true)]
    [InlineData("value", false)]
    [InlineData("priority", false)]
    [InlineData("removed", false)]
    public void MathlibReanchorTracksLocalAttributedInstanceDefinitions(string mutation, bool authorized)
    {
        const string attribute = "@[local instance] ";
        const string source = "namespace N\nclass Box where val : Nat\n"
            + attribute + "def box : Box := ⟨7⟩\n"
            + "theorem a : Box.val = Box.val := rfl\nend N\n";
        var root = ModuleWithReport("A", source, "old local instance use", declarations: ["N.a"]);
        var candidate = root with
        {
            Source = mutation switch
            {
                "value" => source.Replace("⟨7⟩", "⟨8⟩", StringComparison.Ordinal),
                "priority" => source.Replace(attribute, "@[local instance 50] ", StringComparison.Ordinal),
                "removed" => source.Replace(attribute, "", StringComparison.Ordinal),
                _ => source,
            },
            StatementMaterial = "new local instance use",
        };

        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("unchanged", true)]
    [InlineData("value", false)]
    [InlineData("priority", false)]
    [InlineData("removed", false)]
    public void MathlibReanchorTracksImportedScopedAttributedInstanceDefinitions(
        string mutation, bool authorized)
    {
        const string attribute = "@[scoped instance] ";
        var dependency = ModuleWithReport("B", "namespace N\nclass Box where val : Nat\n"
            + attribute + "def box : Box := ⟨7⟩\nend N\n", "scoped instance source",
            declarations: ["N.box"], kind: "def");
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\nopen scoped N\nnamespace M\n"
            + "theorem a : N.Box.val = N.Box.val := rfl\nend M\n", "old scoped instance use",
            declarations: ["M.a"]) with { Imports = ["B"] };
        var candidateDependency = dependency with
        {
            Source = mutation switch
            {
                "value" => dependency.Source.Replace("⟨7⟩", "⟨8⟩", StringComparison.Ordinal),
                "priority" => dependency.Source.Replace(attribute, "@[scoped instance 50] ", StringComparison.Ordinal),
                "removed" => dependency.Source.Replace(attribute, "", StringComparison.Ordinal),
                _ => dependency.Source,
            },
        };

        var result = ValidateMathlibReanchor([root, dependency],
            [root with { StatementMaterial = "new scoped instance use" }, candidateDependency],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }
}
