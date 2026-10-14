using System.Collections.Immutable;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("unchanged", true)]
    [InlineData("fieldType", false)]
    [InlineData("fieldName", false)]
    [InlineData("structure", false)]
    public void MathlibReanchorPreservesCompiledInductiveClassSource(string mutation, bool authorized)
    {
        const string source = "class Carrier where\n  value : Nat\n";
        var baseline = ModuleWithReport("A", source, "old compiled class",
            declarations: ["Carrier"], kind: "inductive");
        var candidate = baseline with
        {
            Source = mutation switch
            {
                "fieldType" => source.Replace("Nat", "Int", StringComparison.Ordinal),
                "fieldName" => source.Replace("value", "other", StringComparison.Ordinal),
                "structure" => source.Replace("class", "structure", StringComparison.Ordinal),
                _ => source,
            },
            StatementMaterial = "new compiled class",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("def")]
    [InlineData("theorem")]
    [InlineData("opaque")]
    public void MathlibReanchorRejectsWrongCompiledClassKind(string kind)
    {
        var baseline = ModuleWithReport("A", "class Carrier where\n  value : Nat\n",
            "old wrong class kind", declarations: ["Carrier"], kind: kind);
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")],
            [baseline with { StatementMaterial = "new wrong class kind" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("", "", true)]
    [InlineData("", "", false)]
    [InlineData("N", "", true)]
    [InlineData("N", "", false)]
    [InlineData("N", "[Inhabited Nat] ", true)]
    [InlineData("N", "[Inhabited Nat] ", false)]
    public void MathlibReanchorKeepsAnonymousInstanceDistinctFromItsClass(
        string scope, string parameters, bool unchanged)
    {
        var source = (scope.Length == 0 ? "" : "namespace " + scope + "\n")
            + "class Carrier where\n  value : Nat\n"
            + "instance " + parameters + ": Carrier := ⟨7⟩\n"
            + (scope.Length == 0 ? "" : "end " + scope + "\n");
        var baseline = ModuleWithReport("A", source, "old class",
            declarations: [scope.Length == 0 ? "Carrier" : scope + ".Carrier"], kind: "inductive");
        var candidate = baseline with
        {
            Source = unchanged ? source : source.Replace("⟨7⟩", "⟨8⟩", StringComparison.Ordinal),
            StatementMaterial = "new class",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(unchanged, result.Authorized);
    }

    [Theory]
    [InlineData(false, true)]
    [InlineData(false, false)]
    [InlineData(true, true)]
    [InlineData(true, false)]
    public void MathlibReanchorTracksAnonymousInstanceImportedDependencies(
        bool transitive, bool unchanged)
    {
        var root = ModuleWithReport("A",
            "import D5.S0.Carrier.B\nclass Carrier where\n  value : Nat\n"
                + "instance : Carrier := ⟨D5.S0.Carrier.seed⟩\n",
            "old class", declarations: ["Carrier"], kind: "inductive") with { Imports = ["B"] };
        var dependency = ModuleWithReport("B",
            (transitive ? "import D5.S0.Carrier.C\n" : "")
                + "namespace D5.S0.Carrier\ndef seed : Nat := "
                + (transitive ? "baseValue" : "7") + "\nend D5.S0.Carrier\n",
            "seed", declarations: ["D5.S0.Carrier.seed"], kind: "def")
            with { Imports = transitive ? ["C"] : [] };
        var leaf = ModuleWithReport("C",
            "namespace D5.S0.Carrier\ndef baseValue : Nat := 7\nend D5.S0.Carrier\n",
            "base", declarations: ["D5.S0.Carrier.baseValue"], kind: "def");
        var candidateDependency = dependency with
        {
            Source = transitive || unchanged ? dependency.Source
                : dependency.Source.Replace("7", "8", StringComparison.Ordinal),
        };
        var candidateLeaf = leaf with
        {
            Source = !transitive || unchanged ? leaf.Source
                : leaf.Source.Replace("7", "8", StringComparison.Ordinal),
        };
        var result = ValidateMathlibReanchor(
            [root, dependency, leaf],
            [root with { StatementMaterial = "new class" }, candidateDependency, candidateLeaf],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(unchanged, result.Authorized);
    }

    [Theory]
    [InlineData(false, true, "")]
    [InlineData(false, false, "")]
    [InlineData(true, true, "")]
    [InlineData(true, false, "")]
    [InlineData(false, true, "public ")]
    [InlineData(false, false, "public ")]
    [InlineData(true, true, "public ")]
    [InlineData(true, false, "public ")]
    public void MathlibReanchorTracksImportedAnonymousInstancesWithoutFrozenDependencies(
        bool transitive, bool unchanged, string importPrefix)
    {
        var root = ModuleWithReport("A",
            importPrefix + "import D5.S0.Carrier.B\ndef a : Nat := (inferInstance : Inhabited Nat).default\n",
            "old default", declarations: ["a"], kind: "def") with { Imports = ["B"] };
        var dependency = ModuleWithReport("B",
            transitive ? importPrefix + "import D5.S0.Carrier.C\ntheorem b : True := by trivial\n"
                : "instance : Inhabited Nat := ⟨7⟩\n",
            "dependency", declarations: [transitive ? "b" : "instInhabitedNat"],
            kind: transitive ? "theorem" : "def") with { Imports = transitive ? ["C"] : [] };
        var leaf = ModuleWithReport("C", "instance : Inhabited Nat := ⟨7⟩\n",
            "leaf", declarations: ["instInhabitedNat"], kind: "def");
        ModuleSpec[] baseline = [root, dependency, leaf];
        ModuleSpec[] candidate =
        [
            root with { StatementMaterial = "new default" },
            dependency with { Source = transitive || unchanged ? dependency.Source
                : dependency.Source.Replace("7", "8", StringComparison.Ordinal) },
            leaf with { Source = !transitive || unchanged ? leaf.Source
                : leaf.Source.Replace("7", "8", StringComparison.Ordinal) },
        ];
        var protectedBase = Snapshot(StateFiles(BuildCatalog(baseline))
            .Where(file => file.Path.Value == "Golden/Frozen/state/" + PathFor("A") + ".json")
            .Concat(ReanchorInputFiles(baseline, ReanchorEnvironment.PinUpgrade, candidate: false)));
        var current = Snapshot(StateFiles(BuildCatalog(candidate))
            .Where(file => file.Path.Value == "Golden/Frozen/state/" + PathFor("A") + ".json")
            .Concat(ReanchorInputFiles(candidate, ReanchorEnvironment.PinUpgrade, candidate: true)));
        var baseState = FrozenStateCatalog.Load(protectedBase);
        Assert.Equal(RepoPathFor("A"), Assert.Single(baseState.Selectors));
        var authorization = new MathlibUpgradeFrozenLedgerReplacementAuthorization(protectedBase, current);

        Assert.Equal(unchanged, authorization.IsAuthorized(
            new[] { RepoPathFor("A") }.ToImmutableHashSet(), baseState, Report(candidate)));
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void MathlibReanchorKeepsImportedAnonymousCommandBindersSeparate(bool unchanged)
    {
        var root = ModuleWithReport("A",
            "import D5.S0.Carrier.B\ndef a : Nat := (inferInstance : Inhabited Nat).default\n",
            "old default", declarations: ["a"], kind: "def") with { Imports = ["B"] };
        var dependency = ModuleWithReport("B",
            "import D5.S0.Carrier.C\nopen D5.S0.Carrier\n"
                + "instance : Inhabited (Nat → Nat) := ⟨fun seed => seed⟩\n"
                + "instance : Inhabited Nat := ⟨seed⟩\n",
            "instances", declarations: ["instInhabitedNat"], kind: "def") with { Imports = ["C"] };
        var leaf = ModuleWithReport("C",
            "namespace D5.S0.Carrier\ndef seed : Nat := 7\nend D5.S0.Carrier\n",
            "seed", declarations: ["D5.S0.Carrier.seed"], kind: "def");
        ModuleSpec[] baseline = [root, dependency, leaf];
        ModuleSpec[] candidate =
        [
            root with { StatementMaterial = "new default" }, dependency,
            leaf with { Source = unchanged ? leaf.Source
                : leaf.Source.Replace("7", "8", StringComparison.Ordinal) },
        ];
        var protectedBase = Snapshot(StateFiles(BuildCatalog(baseline))
            .Where(file => file.Path.Value == "Golden/Frozen/state/" + PathFor("A") + ".json")
            .Concat(ReanchorInputFiles(baseline, ReanchorEnvironment.PinUpgrade, candidate: false)));
        var current = Snapshot(StateFiles(BuildCatalog(candidate))
            .Where(file => file.Path.Value == "Golden/Frozen/state/" + PathFor("A") + ".json")
            .Concat(ReanchorInputFiles(candidate, ReanchorEnvironment.PinUpgrade, candidate: true)));
        var baseState = FrozenStateCatalog.Load(protectedBase);
        Assert.Equal(RepoPathFor("A"), Assert.Single(baseState.Selectors));
        var authorization = new MathlibUpgradeFrozenLedgerReplacementAuthorization(protectedBase, current);

        Assert.Equal(unchanged, authorization.IsAuthorized(
            new[] { RepoPathFor("A") }.ToImmutableHashSet(), baseState, Report(candidate)));
    }

    [Theory]
    [InlineData("7", "8", true)]
    [InlineData("9", "8", false)]
    [InlineData("7", "9", true)]
    public void MathlibReanchorQualifiesDottedDeclarationsInTheirNamespace(
        string firstValue, string secondValue, bool authorized)
    {
        const string original = "namespace One\ndef Inner.value : Nat := 7\nend One\n"
            + "namespace Two\ndef Inner.value : Nat := 8\nend Two\n";
        var baseline = ModuleWithReport("A", original, "old value",
            declarations: ["One.Inner.value"], kind: "def");
        var candidate = baseline with
        {
            Source = original.Replace(":= 7", ":= " + firstValue, StringComparison.Ordinal)
                .Replace(":= 8", ":= " + secondValue, StringComparison.Ordinal),
            StatementMaterial = "new value",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void MathlibReanchorTracksQualifiedDefinitionDependencies(bool unchanged)
    {
        const string original = "namespace Two\ndef Inner.value : Nat := 7\nend Two\n"
            + "namespace One\ndef Inner.value : Nat := Two.Inner.value\nend One\n";
        var baseline = ModuleWithReport("A", original, "old value",
            declarations: ["One.Inner.value"], kind: "def");
        var candidate = baseline with
        {
            Source = unchanged ? original : original.Replace("7", "8", StringComparison.Ordinal),
            StatementMaterial = "new value",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(unchanged, result.Authorized);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void MathlibReanchorRetainsExplicitRootDeclarationNames(bool unchanged)
    {
        const string original = "namespace One\ndef _root_.value : Nat := 7\nend One\n";
        var baseline = ModuleWithReport("A", original, "old value",
            declarations: ["value"], kind: "def");
        var candidate = baseline with
        {
            Source = unchanged ? original : original.Replace("7", "8", StringComparison.Ordinal),
            StatementMaterial = "new value",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(unchanged, result.Authorized);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void MathlibReanchorRetainsAnonymousOnlyModuleSource(bool unchanged)
    {
        const string source = "instance : Inhabited Nat := ⟨7⟩\n";
        var baseline = ModuleWithReport("A", source, "old instance",
            declarations: ["instInhabitedNat"], kind: "def");
        var candidate = baseline with
        {
            Source = unchanged ? source : source.Replace("7", "8", StringComparison.Ordinal),
            Declarations = ["instInhabitedNat_drift"],
            StatementMaterial = "new instance",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.Equal(unchanged, result.Authorized);
    }

    [Theory]
    [InlineData("instance : Inhabited Nat := ⟨7⟩\n", "missing")]
    [InlineData("instance (priority := 10) named : Inhabited Nat := ⟨7⟩\n", "named")]
    public void MathlibReanchorDoesNotUseAnonymousSourceForUnresolvedNamedDeclaration(
        string source, string name)
    {
        var baseline = ModuleWithReport("A", source, "old named root",
            declarations: [name], kind: "def");
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")],
            [baseline with { StatementMaterial = "new named root" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRefusesAnonymousInstanceUnsupportedImportedSyntax()
    {
        var root = ModuleWithReport("A",
            "import D5.S0.Carrier.B\nclass Carrier where\n  value : Nat\n"
                + "instance : Carrier := ⟨payload⟩\n",
            "old class", declarations: ["Carrier"], kind: "inductive") with { Imports = ["B"] };
        var dependency = ModuleWithReport("B",
            "notation \"payload\" => 7\ntheorem b : True := by trivial\n", "notation");
        var result = ValidateMathlibReanchor(
            [root, dependency], [root with { StatementMaterial = "new class" }, dependency],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.False(result.Authorized);
    }

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
