using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    private const string QuotedModuleGenerator = "macro \"generated_value\" : term =>\n"
        + "  pure (Lean.mkIdent (Lean.mkPrivateNameCore `D5.S0.Carrier.B `N.hidden))\n";

    [Theory]
    [InlineData(false, "unchanged", true)]
    [InlineData(true, "unchanged", true)]
    [InlineData(false, "value", false)]
    [InlineData(true, "value", false)]
    [InlineData(false, "type", false)]
    [InlineData(true, "type", false)]
    [InlineData(false, "proof", false)]
    [InlineData(true, "proof", false)]
    [InlineData(false, "owner-proof", false)]
    [InlineData(true, "owner-proof", false)]
    [InlineData(false, "owner-comment", false)]
    [InlineData(true, "owner-comment", false)]
    [InlineData(false, "parent-comment", false)]
    [InlineData(true, "parent-comment", false)]
    [InlineData(false, "position", false)]
    [InlineData(true, "position", false)]
    [InlineData(false, "bridge", true)]
    [InlineData(true, "bridge", false)]
    [InlineData(false, "unrelated", false)]
    [InlineData(true, "unrelated", false)]
    public void MathlibReanchorBindsQuotedModuleSourceClosures(bool transitive, string mutation, bool authorized)
    {
        var dependency = ModuleWithReport("B", "namespace N\ndef seed : Nat := 7\n"
            + "private theorem hidden : True := by trivial\ndef unrelated : Nat := 11\nend N\n",
            "quoted module", declarations: ["N.seed"], kind: "def");
        var bridge = Module("C", "import D5.S0.Carrier.B\n", ["B"]);
        var owner = ModuleWithReport("A", "import D5.S0.Carrier." + (transitive ? "C" : "B")
            + "\n" + QuotedModuleGenerator + "theorem a : True := by trivial\n",
            "old generator", declarations: ["termGenerated_value"], kind: "def")
            with { Imports = [transitive ? "C" : "B"] };
        var candidateDependency = dependency with
        {
            Source = mutation switch
            {
                "value" => dependency.Source.Replace("7", "8", StringComparison.Ordinal),
                "type" => dependency.Source.Replace("seed : Nat", "seed : Int", StringComparison.Ordinal),
                "proof" => dependency.Source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
                "parent-comment" => dependency.Source + "-- context\n",
                "unrelated" => dependency.Source.Replace("11", "12", StringComparison.Ordinal),
                _ => dependency.Source,
            },
        };
        var candidateOwner = owner with
        {
            Source = mutation switch
            {
                "owner-proof" => owner.Source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
                "owner-comment" => owner.Source + "-- context\n",
                "position" => "\n" + owner.Source,
                _ => owner.Source,
            },
            StatementMaterial = "new generator",
        };
        var candidateBridge = bridge with { Source = mutation == "bridge" ? bridge.Source + "-- context\n" : bridge.Source };
        var result = ValidateMathlibReanchor([owner, dependency, bridge],
            [candidateOwner, candidateDependency, candidateBridge], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("D5.S0.Carrier.B", true, true, true)]
    [InlineData("D5.S0.Carrier.B", false, true, false)]
    [InlineData("D5.S0.Carrier.B", true, false, false)]
    [InlineData("D5.S0.Carrier.Missing", true, true, false)]
    [InlineData("D5.S0.Carrier.BExtra", true, true, false)]
    [InlineData("D5.S0.Carrier.B.missing", true, true, false)]
    [InlineData("D5.S0.Carrier", true, true, false)]
    [InlineData("D5.S0.Carrier.A", true, true, false)]
    public void MathlibReanchorRequiresAnExactImportedQuotedModule(
        string name, bool quoted, bool imported, bool authorized)
    {
        var dependency = Module("B", "namespace N\ndef seed : Nat := 7\nend N\n");
        var owner = ModuleWithReport("A", (imported ? "import D5.S0.Carrier.B\n" : "")
            + "macro \"generated_value\" : term =>\n"
            + "  pure (Lean.mkIdent (" + (quoted ? "`" : "") + name + "))\n"
            + "theorem a : True := by trivial\n", "old quoted name",
            declarations: ["termGenerated_value"], kind: "def") with { Imports = imported ? ["B"] : [] };
        var result = ValidateMathlibReanchor([owner, dependency],
            [owner with { StatementMaterial = "new quoted name" }, dependency],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("double-quote")]
    [InlineData("mixed")]
    public void MathlibReanchorRefusesResolvedOrMixedModuleQuotations(string quotation)
    {
        var dependency = Module("B", "namespace N\ndef seed : Nat := 7\nend N\n");
        var body = quotation == "double-quote" ? "pure (Lean.mkIdent ``D5.S0.Carrier.B)"
            : "let unquoted := D5.S0.Carrier.B; pure (Lean.mkIdent `D5.S0.Carrier.B)";
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.B\nmacro \"generated_value\" : term =>\n  "
            + body + "\ntheorem a : True := by trivial\n", "old mixed name",
            declarations: ["termGenerated_value"], kind: "def") with { Imports = ["B"] };
        var result = ValidateMathlibReanchor([owner, dependency],
            [owner with { StatementMaterial = "new mixed name" }, dependency], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("unchanged", true)]
    [InlineData("owner-proof", false)]
    [InlineData("owner-comment", false)]
    [InlineData("owner-position", false)]
    [InlineData("bridge", false)]
    public void MathlibReanchorBindsQuotedHelperToExtractionOwner(string mutation, bool authorized)
    {
        var dependency = Module("C", "namespace N\nprivate theorem hidden : True := by trivial\nend N\n");
        var helper = ModuleWithReport("B", "import D5.S0.Carrier.C\nnamespace N\n"
            + "def moduleName : Lean.Name := `D5.S0.Carrier.C\nend N\n", "helper module",
            declarations: ["N.moduleName"], kind: "def") with { Imports = ["C"] };
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.B\n"
            + "theorem a : N.moduleName = N.moduleName := by rfl\n", "old helper consumer") with { Imports = ["B"] };
        var candidateOwner = owner with
        {
            StatementMaterial = "new helper consumer",
            Source = mutation switch
            {
                "owner-proof" => owner.Source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal),
                "owner-comment" => owner.Source + "-- context\n",
                "owner-position" => "\n" + owner.Source,
                _ => owner.Source,
            },
        };
        var candidateHelper = helper with { Source = mutation == "bridge" ? helper.Source + "-- context\n" : helper.Source };
        var result = ValidateMathlibReanchor([owner, helper, dependency], [candidateOwner, candidateHelper, dependency],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }
}
