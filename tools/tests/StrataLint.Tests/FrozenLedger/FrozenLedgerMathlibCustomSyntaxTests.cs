using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData(false, "unchanged", true)]
    [InlineData(true, "unchanged", true)]
    [InlineData(false, "owner-proof", false)]
    [InlineData(true, "owner-proof", false)]
    [InlineData(false, "owner-comment", false)]
    [InlineData(true, "owner-comment", false)]
    [InlineData(false, "owner-position", false)]
    [InlineData(true, "owner-position", false)]
    [InlineData(false, "provider-body", false)]
    [InlineData(true, "provider-body", false)]
    [InlineData(false, "provider-proof", false)]
    [InlineData(true, "provider-proof", false)]
    [InlineData(false, "provider-comment", false)]
    [InlineData(true, "provider-comment", false)]
    [InlineData(false, "unrelated-definition", false)]
    [InlineData(true, "unrelated-definition", false)]
    [InlineData(false, "bridge", true)]
    [InlineData(true, "bridge", false)]
    [InlineData(false, "unimported", true)]
    [InlineData(true, "unimported", true)]
    public void MathlibReanchorBindsCustomSyntaxSourceClosures(bool transitive, string mutation, bool authorized)
    {
        var provider = Module("B", "macro \"custom_value\" : term => `(7)\n"
            + "private theorem hidden : True := by trivial\ndef unrelated : Nat := 11\n");
        var bridge = Module("C", "import D5.S0.Carrier.B\n", ["B"]);
        var unimported = Module("D", "def other : Nat := 3\n");
        var owner = ModuleWithReport("A", "import D5.S0.Carrier." + (transitive ? "C" : "B")
            + "\ndef value : Nat := custom_value\ntheorem a : True := by trivial\n",
            "old custom value", declarations: ["value"], kind: "def") with { Imports = [transitive ? "C" : "B"] };
        var candidateOwner = owner with
        {
            Source = mutation switch
            {
                "owner-proof" => owner.Source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
                "owner-comment" => owner.Source + "-- owner context\n",
                "owner-position" => "\n" + owner.Source,
                _ => owner.Source,
            },
            StatementMaterial = "new custom value",
        };
        var candidateProvider = provider with
        {
            Source = mutation switch
            {
                "provider-body" => provider.Source.Replace("(7)", "(8)", StringComparison.Ordinal),
                "provider-proof" => provider.Source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
                "provider-comment" => provider.Source + "-- provider context\n",
                "unrelated-definition" => provider.Source.Replace("11", "12", StringComparison.Ordinal),
                _ => provider.Source,
            },
        };
        var result = ValidateMathlibReanchor([owner, provider, bridge, unimported],
            [candidateOwner, candidateProvider,
                bridge with { Source = mutation == "bridge" ? bridge.Source + "-- bridge context\n" : bridge.Source },
                unimported with { Source = mutation == "unimported" ? unimported.Source + "-- other context\n" : unimported.Source }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("unchanged", true)]
    [InlineData("owner-proof", false)]
    [InlineData("owner-comment", false)]
    [InlineData("owner-position", false)]
    [InlineData("helper-comment", false)]
    public void MathlibReanchorBindsCustomSyntaxHelperToExtractionOwner(string mutation, bool authorized)
    {
        var provider = Module("C", "macro \"custom_value\" : term => `(7)\n");
        var helper = Module("B", "import D5.S0.Carrier.C\nnamespace N\n"
            + "def seed : Nat := custom_value\nend N\n", ["C"]);
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.B\n"
            + "theorem a : N.seed = N.seed := by rfl\n", "old helper consumer") with { Imports = ["B"] };
        var result = ValidateMathlibReanchor([owner, helper, provider],
            [owner with
            {
                Source = mutation switch
                {
                    "owner-proof" => owner.Source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal),
                    "owner-comment" => owner.Source + "-- owner context\n",
                    "owner-position" => "\n" + owner.Source,
                    _ => owner.Source,
                },
                StatementMaterial = "new helper consumer",
            }, helper with { Source = mutation == "helper-comment" ? helper.Source + "-- helper context\n" : helper.Source }, provider],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData(false, "unresolved")]
    [InlineData(true, "unresolved")]
    [InlineData(false, "missing-root")]
    [InlineData(true, "missing-root")]
    [InlineData(false, "wrong-kind")]
    public void MathlibReanchorCustomSyntaxPreservesRootAndDependencyRejections(bool generated, string invalid)
    {
        var source = "import D5.S0.Carrier.B\n" + (generated
            ? "macro \"generated_value\" : term => `(custom_value + D5.S0.Carrier.missing)\n"
                + "theorem sentinel : True := by trivial\n"
            : "def value : Nat := custom_value + D5.S0.Carrier.missing\n");
        if (invalid != "unresolved") source = source.Replace(" + D5.S0.Carrier.missing", "", StringComparison.Ordinal);
        var owner = ModuleWithReport("A", source, "old invalid custom source",
            declarations: [invalid == "missing-root" ? "missing" : generated ? "termGenerated_value" : "value"],
            kind: invalid == "wrong-kind" ? "theorem" : "def") with { Imports = ["B"] };
        var provider = Module("B", "macro \"custom_value\" : term => `(7)\n");
        var result = ValidateMathlibReanchor([owner, provider],
            [owner with { StatementMaterial = "new invalid custom source" }, provider], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData(")")]
    [InlineData("]")]
    [InlineData("⊢")]
    [InlineData("&")]
    public void MathlibReanchorBindsVisibleCustomDelimiterSources(string literal)
    {
        var provider = Module("B", "syntax \"" + literal + "\" : term\n");
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.B\n"
            + "def value : Nat := (7) + (0 : Nat)\n", "old delimiter value", declarations: ["value"], kind: "def")
            with { Imports = ["B"] };
        if (literal != ")") owner = owner with
        {
            Source = literal == "]" ? "import D5.S0.Carrier.B\n"
                + "def value : List Nat := [7]\n" : owner.Source.Replace("(7)", literal, StringComparison.Ordinal),
        };
        var unchanged = ValidateMathlibReanchor([owner, provider],
            [owner with { StatementMaterial = "new delimiter value" }, provider], ["A"], ReanchorEnvironment.PinUpgrade);
        var changed = ValidateMathlibReanchor([owner, provider],
            [owner with { StatementMaterial = "new delimiter value" }, provider with { Source = provider.Source + "-- changed syntax\n" }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.True(unchanged.Authorized);
        Assert.False(changed.Authorized);
    }

    [Theory]
    [InlineData("body", "unchanged", true)]
    [InlineData("body", "provider", false)]
    [InlineData("body", "proof", false)]
    [InlineData("body", "comment", false)]
    [InlineData("macro_rules", "unchanged", true)]
    [InlineData("macro_rules", "provider", false)]
    [InlineData("macro_rules", "proof", false)]
    [InlineData("macro_rules", "comment", false)]
    [InlineData("elab_rules : term", "unchanged", true)]
    [InlineData("elab_rules : term", "provider", false)]
    [InlineData("elab_rules : term", "proof", false)]
    [InlineData("elab_rules : term", "comment", false)]
    [InlineData("instance", "unchanged", true)]
    [InlineData("instance", "provider", false)]
    [InlineData("instance", "proof", false)]
    [InlineData("instance", "comment", false)]
    public void MathlibReanchorBindsCustomGeneratorAndInstanceSources(string form, string mutation, bool authorized)
    {
        var prefix = form switch
        {
            "body" => "macro \"generated_value\" : term => `(custom_value)\n",
            "instance" => "class Carrier where\n  value : Nat\ninstance : Carrier := ⟨custom_value⟩\n",
            _ => form + "\n  | `(custom_value) => `(7)\n",
        };
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.B\n" + prefix
            + "theorem a : True := by trivial\n", "old syntax consumer",
            declarations: [form == "instance" ? "Carrier" : "termGenerated_value"],
            kind: form == "instance" ? "inductive" : "def") with { Imports = ["B"] };
        var provider = Module("B", "macro \"custom_value\" : term => `(7)\n");
        var result = ValidateMathlibReanchor([owner, provider],
            [owner with
            {
                Source = mutation switch
                {
                    "proof" => owner.Source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
                    "comment" => owner.Source + "-- context\n",
                    _ => owner.Source,
                },
                StatementMaterial = "new syntax consumer",
            }, provider with { Source = mutation == "provider" ? provider.Source.Replace("(7)", "(8)", StringComparison.Ordinal) : provider.Source }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

}
