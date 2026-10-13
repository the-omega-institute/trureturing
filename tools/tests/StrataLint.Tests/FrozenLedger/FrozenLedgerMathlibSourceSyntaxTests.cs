using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("pre_transition", "PredictiveThermodynamic.tacticPre_transition")]
    [InlineData("parser_transition", "PredictiveThermodynamic.tacticParser_transition")]
    public void MathlibReanchorBindsTacticGeneratedRootsToTheirModuleSource(
        string literal, string generatedName)
    {
        var source = "namespace PredictiveThermodynamic\nmacro \"" + literal
            + "\" : tactic => `(tactic| rfl)\ntheorem a : True := by trivial\nend PredictiveThermodynamic\n";
        var baseline = ModuleWithReport("A", source, "old generated tactic",
            declarations: [generatedName], kind: "def");
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")],
            [baseline with
            {
                Source = source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
                StatementMaterial = "new generated tactic",
            }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("rfl", "simp")]
    [InlineData("pre_transition", "other_transition")]
    public void MathlibReanchorRejectsChangedTacticGeneratorCommand(string before, string after)
    {
        const string source = "macro \"pre_transition\" : tactic => `(tactic| rfl)\ntheorem a : True := by trivial\n";
        var baseline = ModuleWithReport("A", source, "old generated tactic",
            declarations: ["tacticPre_transition"], kind: "def");
        var candidate = baseline with
        {
            Source = source.Replace(before, after, StringComparison.Ordinal),
            StatementMaterial = "new generated tactic",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void MathlibReanchorTracksDefinitionsUsedOnlyByGeneratorCommands(
        bool transitive, bool unchanged)
    {
        var root = ModuleWithReport("A",
            "import D5.S0.Carrier.B\nmacro \"generated_value\" : term => `(D5.S0.Carrier.value)\n"
                + "theorem a : True := by trivial\n",
            "old generated value", declarations: ["termGenerated_value"], kind: "def")
            with { Imports = ["B"] };
        var dependency = ModuleWithReport("B",
            (transitive ? "import D5.S0.Carrier.C\n" : "")
                + "namespace D5.S0.Carrier\ndef value : Nat := "
                + (transitive ? "seed" : "7") + "\nend D5.S0.Carrier\n",
            "value", declarations: ["D5.S0.Carrier.value"], kind: "def")
            with { Imports = transitive ? ["C"] : [] };
        var seed = ModuleWithReport("C",
            "namespace D5.S0.Carrier\ndef seed : Nat := 7\nend D5.S0.Carrier\n",
            "seed", declarations: ["D5.S0.Carrier.seed"], kind: "def");
        var changedDependency = dependency with
        {
            Source = unchanged || transitive ? dependency.Source
                : dependency.Source.Replace("7", "8", StringComparison.Ordinal),
        };
        var changedSeed = seed with
        {
            Source = unchanged || !transitive ? seed.Source
                : seed.Source.Replace("7", "8", StringComparison.Ordinal),
        };
        var result = ValidateMathlibReanchor(
            [root, dependency, seed],
            [root with { StatementMaterial = "new generated value" }, changedDependency, changedSeed],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(unchanged, result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRefusesTacticNameWithoutATacticGenerator()
    {
        var baseline = ModuleWithReport("A", "theorem a : True := by trivial\n",
            "old unsupported root", declarations: ["tacticMissing"], kind: "def");
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")],
            [baseline with { StatementMaterial = "new unsupported root" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorDoesNotMistakeQuotedTacticForTheGeneratorCategory()
    {
        var baseline = ModuleWithReport("A",
            "macro \"generated_value\" : term => `(tactic| rfl)\ntheorem a : True := by trivial\n",
            "old unsupported root", declarations: ["tacticMissing"], kind: "def");
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")],
            [baseline with { StatementMaterial = "new unsupported root" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorRefusesCustomSyntaxUsedOnlyInGeneratorBodies(bool imported)
    {
        const string inner = "macro \"inner_value\" : term => `(7)\n";
        var root = ModuleWithReport("A",
            (imported ? "import D5.S0.Carrier.B\n" : inner)
                + "macro \"generated_value\" : term => `(inner_value)\ntheorem a : True := by trivial\n",
            "old generated value", declarations: ["termGenerated_value"], kind: "def")
            with { Imports = imported ? ["B"] : [] };
        var dependency = Module("B", (imported ? inner : "") + "theorem b : True := by trivial\n");
        var result = ValidateMathlibReanchor(
            [root, dependency],
            [root with { StatementMaterial = "new generated value" }, dependency],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("macro_rules")]
    [InlineData("elab_rules : term")]
    public void MathlibReanchorRefusesCustomSyntaxUsedOnlyInGeneratorRulePatterns(string command)
    {
        var root = ModuleWithReport("A",
            "import D5.S0.Carrier.B\n" + command + "\n  | `(inner_value) => `(7)\n"
                + "theorem a : True := by trivial\n",
            "old generated value", declarations: ["termGenerated_value"], kind: "def")
            with { Imports = ["B"] };
        var dependency = Module("B",
            "macro \"inner_value\" : term => `(7)\ntheorem b : True := by trivial\n");
        var result = ValidateMathlibReanchor(
            [root, dependency],
            [root with { StatementMaterial = "new generated value" }, dependency],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorTracksDefinitionsInWrappedGeneratorCommands(bool unchanged)
    {
        var root = ModuleWithReport("A",
            "import D5.S0.Carrier.B\nset_option maxRecDepth 1000 in\n"
                + "  macro \"generated_value\" : term => `(D5.S0.Carrier.value)\n"
                + "theorem a : True := by trivial\n",
            "old generated value", declarations: ["termGenerated_value"], kind: "def")
            with { Imports = ["B"] };
        var dependency = ModuleWithReport("B",
            "namespace D5.S0.Carrier\ndef value : Nat := 7\nend D5.S0.Carrier\n",
            "value", declarations: ["D5.S0.Carrier.value"], kind: "def");
        var result = ValidateMathlibReanchor(
            [root, dependency],
            [root with { StatementMaterial = "new generated value" }, dependency with
            {
                Source = unchanged ? dependency.Source
                    : dependency.Source.Replace("7", "8", StringComparison.Ordinal),
            }],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(unchanged, result.Authorized);
    }

    [Theory]
    [InlineData("7", true)]
    [InlineData("8", false)]
    public void MathlibReanchorRetainsDataInTypesContainingEquality(string value, bool accepted)
    {
        const string original = "def a : Nat := by\n  have h : (0 : Nat) = 0 ×' Nat := by\n    exact ⟨rfl, 7⟩\n  exact h.2\n";
        var candidate = original.Replace("rfl, 7", "rfl, " + value, StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", original, "old Nat", kind: "def"), Module("B")],
            [ModuleWithReport("A", candidate, "new Nat", kind: "def"), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(accepted, result.Authorized);
    }

    [Theory]
    [InlineData("a.eq_def", "True", true)]
    [InlineData("a.eq_def", "False", false)]
    [InlineData("a_assoc", "True", true)]
    [InlineData("a_assoc", "False", false)]
    public void MathlibReanchorGeneratedNamesRetainTheWholeSourceProposition(
        string generatedName, string proposition, bool accepted)
    {
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", "theorem a : True := by exact True.intro\n",
                "old generated", declarations: [generatedName]), Module("B")],
            [ModuleWithReport("A", "theorem a : " + proposition + " := by trivial\n",
                "new generated", declarations: [generatedName]), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(accepted, result.Authorized);
    }

    [Theory]
    [InlineData("/- declaration -/ ", "")]
    [InlineData("public ", "")]
    [InlineData("@[expose] public section\n", "end\n")]
    [InlineData("noncomputable section\n", "end\n")]
    [InlineData("  ", "")]
    [InlineData("set_option autoImplicit false in ", "")]
    public void MathlibReanchorReadsCommandPrefixesWithoutLosingTheStatement(
        string prefix, string suffix)
    {
        var original = prefix + "lemma a : True := by exact True.intro\n" + suffix;
        var candidate = prefix + "lemma a : True := by trivial\n" + suffix;
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", original, "old True"), Module("B")],
            [ModuleWithReport("A", candidate, "new True"), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.True(result.Authorized);

        var weakened = ValidateMathlibReanchor(
            [ModuleWithReport("A", prefix + "lemma a : False := by contradiction\n" + suffix,
                "old False"), Module("B")],
            [ModuleWithReport("A", candidate, "new True"), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(weakened.Authorized);
    }

    [Theory]
    [InlineData("7", false)]
    [InlineData("8", false)]
    public void MathlibReanchorRefusesUnclassifiedLocalEqualityProofBodyChanges(string value, bool accepted)
    {
        const string original = "def a : Nat := by\n  have h : (0 : Nat) = 0 := by\n    rfl\n  exact 7\n";
        var candidate = "def a : Nat := by\n  have h : (0 : Nat) = 0 := by\n    simp\n  exact " + value + "\n";
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", original, "old Nat", kind: "def"), Module("B")],
            [ModuleWithReport("A", candidate, "new Nat", kind: "def"), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(accepted, result.Authorized);
    }
}
