using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    private const string ImportedInductionFunction = "def recurse : Nat → Nat\n"
        + "  | 0 => seed\n  | n + 1 => recurse n + seed\n";

    [Theory]
    [InlineData(false, "unchanged", true)]
    [InlineData(false, "source-position", false)]
    [InlineData(false, "source-comment", false)]
    [InlineData(false, "bridge", true)]
    [InlineData(false, "body", false)]
    [InlineData(false, "seed", false)]
    [InlineData(false, "type", false)]
    [InlineData(false, "removed", false)]
    [InlineData(false, "unrelated", false)]
    [InlineData(false, "proof", false)]
    [InlineData(true, "unchanged", true)]
    [InlineData(true, "source-position", false)]
    [InlineData(true, "source-comment", false)]
    [InlineData(true, "bridge", false)]
    [InlineData(true, "body", false)]
    [InlineData(true, "seed", false)]
    [InlineData(true, "type", false)]
    [InlineData(true, "removed", false)]
    [InlineData(true, "unrelated", false)]
    [InlineData(true, "proof", false)]
    public void MathlibReanchorTracksImportedFunctionInductionSources(bool transitive, string mutation, bool authorized)
    {
        var dependency = ModuleWithReport("B", "namespace N\ndef seed : Nat := 1\n"
            + ImportedInductionFunction + "def unrelated : Nat := 7\nend N\n", "function definition",
            declarations: ["N.recurse"], kind: "def");
        var bridge = Module("C", "import D5.S0.Carrier.B\ntheorem c : True := by trivial\n", ["B"]);
        var owner = ModuleWithReport("A", "import D5.S0.Carrier." + (transitive ? "C" : "B")
            + "\ntheorem a (n : Nat) : N.recurse n = n + 1 := by\n"
            + "  fun_induction N.recurse n <;> simp_all [N.recurse, N.seed]\n",
            "old imported function induction", declarations: ["N.recurse.induct_unfolding"])
            with { Imports = [transitive ? "C" : "B"] };
        var candidateDependency = dependency with
        {
            Source = mutation switch
            {
                "body" => dependency.Source.Replace("recurse n + seed", "recurse n + seed + 1", StringComparison.Ordinal),
                "seed" => dependency.Source.Replace("seed : Nat := 1", "seed : Nat := 2", StringComparison.Ordinal),
                "type" => dependency.Source.Replace("recurse : Nat → Nat", "recurse : Nat → Int", StringComparison.Ordinal),
                "removed" => dependency.Source.Replace(ImportedInductionFunction, "", StringComparison.Ordinal),
                "unrelated" => dependency.Source.Replace("unrelated : Nat := 7", "unrelated : Nat := 8", StringComparison.Ordinal),
                _ => dependency.Source,
            },
        };
        var candidateOwner = owner with
        {
            Source = mutation switch
            {
                "proof" => owner.Source.Replace("simp_all", "simp_all only", StringComparison.Ordinal),
                "source-position" => "\n" + owner.Source,
                "source-comment" => owner.Source + "-- source context\n",
                _ => owner.Source,
            },
            StatementMaterial = "new imported function induction",
        };
        var candidateBridge = bridge with { Source = mutation == "bridge" ? "\n" + bridge.Source : bridge.Source };
        var result = ValidateMathlibReanchor([owner, dependency, bridge], [candidateOwner, candidateDependency, candidateBridge],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("owner")]
    [InlineData("parent")]
    [InlineData("bridge")]
    [InlineData("declaration-free-bridge")]
    public void MathlibReanchorTracksExplicitImportedInductionGeneration(string location)
    {
        const string generation = "run_cmd Lean.Elab.Command.liftCoreM do\n"
            + "  Lean.addDecl (.thmDecl {\n"
            + "    name := `N.recurse.induct_unfolding\n"
            + "    levelParams := []\n"
            + "    type := Lean.mkConst ``True\n"
            + "    value := Lean.mkConst ``True.intro })\n";
        const string replacement = "run_cmd Lean.Elab.Command.liftCoreM do\n"
            + "  Lean.addDecl (.thmDecl {\n"
            + "    name := `N.recurse.induct_unfolding\n"
            + "    levelParams := []\n"
            + "    type := Lean.mkApp2 (Lean.mkConst ``And) (Lean.mkConst ``True) (Lean.mkConst ``True)\n"
            + "    value := Lean.mkApp4 (Lean.mkConst ``And.intro) (Lean.mkConst ``True)\n"
            + "      (Lean.mkConst ``True) (Lean.mkConst ``True.intro) (Lean.mkConst ``True.intro) })\n";
        var dependency = ModuleWithReport("B", "namespace N\ndef seed : Nat := 1\n"
            + ImportedInductionFunction + "end N\n" + (location == "parent" ? generation : ""),
            "function definition", declarations: ["N.recurse"], kind: "def");
        var bridge = Module("C", "import D5.S0.Carrier.B\n"
            + (location == "declaration-free-bridge" ? "" : "theorem c : True := by trivial\n")
            + (location is "bridge" or "declaration-free-bridge" ? generation : ""), ["B"]);
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.C\ntheorem a : True := by trivial\n"
            + (location == "owner" ? generation : ""), "old explicit generator",
            declarations: ["N.recurse.induct_unfolding"]) with { Imports = ["C"] };
        var candidateOwner = owner with
        {
            Source = owner.Source.Replace(generation, replacement, StringComparison.Ordinal),
            StatementMaterial = "changed explicit generator",
        };
        var candidateDependency = dependency with
        {
            Source = dependency.Source.Replace(generation, replacement, StringComparison.Ordinal),
        };
        var candidateBridge = bridge with
        {
            Source = bridge.Source.Replace(generation, replacement, StringComparison.Ordinal),
        };
        var result = ValidateMathlibReanchor([owner, dependency, bridge],
            [candidateOwner, candidateDependency, candidateBridge], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("ns(ns(ns(n0,1:N),7:recurse),16:induct_unfolding)", true)]
    [InlineData("ns(ns(nn(ns(n0,1:N),0),7:recurse),16:induct_unfolding)", false)]
    [InlineData("ns(nn(ns(ns(n0,1:N),7:recurse),0),16:induct_unfolding)", false)]
    [InlineData("nn(ns(ns(ns(n0,1:N),7:recurse),16:induct_unfolding),0)", false)]
    [InlineData("ns(ns(n0,9:N.recurse),16:induct_unfolding)", false)]
    public void MathlibReanchorRequiresExactImportedInductionNameSegments(string nameKey, bool supported)
    {
        var catalog = LeanSourceCatalog.Parse(Snapshot([
            TextFile(PathFor("A"), "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n"),
            TextFile(PathFor("B"), "namespace N\ndef seed : Nat := 1\n" + ImportedInductionFunction + "end N\n"),
        ]));
        var recorded = new FrozenDeclaration(nameKey, "theorem");
        if (supported)
            Assert.NotEmpty(catalog.ExtractPropositionSource(RepoPathFor("A"), [recorded]));
        else
            Assert.Throws<LeanSourceExtractionException>(() => catalog.ExtractPropositionSource(RepoPathFor("A"), [recorded]));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorTracksImportedTacticInductionGeneration(bool sourcePositionOnly)
    {
        const string generator = "elab \"generateInduction\" : tactic => do\n"
            + "  let fromNewline := (← Lean.getFileMap).source.startsWith \"\\n\"\n"
            + "  let (proposition, proof) := if fromNewline then\n"
            + "    (Lean.mkConst ``True, Lean.mkConst ``True.intro)\n"
            + "    else (Lean.mkApp2 (Lean.mkConst ``And) (Lean.mkConst ``True) (Lean.mkConst ``True),\n"
            + "      Lean.mkApp4 (Lean.mkConst ``And.intro) (Lean.mkConst ``True)\n"
            + "        (Lean.mkConst ``True) (Lean.mkConst ``True.intro) (Lean.mkConst ``True.intro))\n"
            + "  Lean.addDecl (.thmDecl { name := `N.recurse.induct_unfolding, levelParams := [],\n"
            + "    type := proposition, value := proof })\n";
        var dependency = ModuleWithReport("B", "namespace N\ndef seed : Nat := 1\n"
            + ImportedInductionFunction + "end N\n", "function source", declarations: ["N.recurse"], kind: "def");
        var bridge = Module("C", "import D5.S0.Carrier.B\n" + generator, ["B"]);
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.C\ntheorem a : True := by\n"
            + "  generateInduction\n  trivial\n", "old generated type", declarations: ["N.recurse.induct_unfolding"])
            with { Imports = ["C"] };
        var candidateOwner = owner with
        {
            Source = sourcePositionOnly ? "\n" + owner.Source : owner.Source,
            StatementMaterial = "changed generated type",
        };
        var candidateBridge = bridge with
        {
            Source = sourcePositionOnly ? bridge.Source
                : bridge.Source.Replace("if fromNewline then", "if !fromNewline then", StringComparison.Ordinal),
        };
        var result = ValidateMathlibReanchor([owner, dependency, bridge], [candidateOwner, dependency, candidateBridge],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesNamedGeneratorsWithInductionSuffix(bool changeExpansion)
    {
        const string source = "local notation (name := seedNotation.induct_unfolding) \"seed_alias\" => (1 : Nat)\n"
            + "theorem a : True := by trivial\n";
        var owner = ModuleWithReport("A", source, "old named generator",
            declarations: ["seedNotation.induct_unfolding"], kind: "def");
        var candidate = owner with
        {
            Source = changeExpansion ? source.Replace("(1 : Nat)", "(2 : Nat)", StringComparison.Ordinal) : source,
            StatementMaterial = "new named generator",
        };
        var result = ValidateMathlibReanchor([owner], [candidate], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeExpansion, result.Authorized);
    }

    [Theory]
    [InlineData("termFunction")]
    [InlineData("_aux_function")]
    public void MathlibReanchorBindsImportedInductionBeforeGeneratedNameHeuristics(string parentName)
    {
        var dependency = ModuleWithReport("B", "namespace N\ndef seed : Nat := 1\n"
            + ImportedInductionFunction.Replace("recurse", parentName, StringComparison.Ordinal) + "end N\n",
            "parent function", declarations: ["N." + parentName], kind: "def");
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n",
            "old imported induction", declarations: ["N." + parentName + ".induct_unfolding"])
            with { Imports = ["B"] };
        var candidate = dependency with
        {
            Source = dependency.Source.Replace("+ seed", "+ seed + 1", StringComparison.Ordinal),
        };
        var result = ValidateMathlibReanchor([owner, dependency],
            [owner with { StatementMaterial = "changed imported induction" }, candidate], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("unimported")]
    [InlineData("quoted-parent")]
    [InlineData("missing")]
    [InlineData("private")]
    [InlineData("unsafe")]
    [InlineData("meta")]
    [InlineData("partial")]
    [InlineData("private-root")]
    [InlineData("opaque")]
    [InlineData("abbrev")]
    [InlineData("theorem")]
    [InlineData("duplicate")]
    [InlineData("explicit")]
    [InlineData("namespace")]
    [InlineData("suffix")]
    [InlineData("kind")]
    public void MathlibReanchorRefusesUnboundImportedInductionNames(string boundary)
    {
        var function = boundary switch
        {
            "missing" => "def other : Nat := 1\n",
            "quoted-parent" => "def quoted : MacroM (TSyntax `command) := `(command|\n"
                + ImportedInductionFunction + ")\n",
            "private" => "private " + ImportedInductionFunction,
            "unsafe" => "unsafe " + ImportedInductionFunction,
            "meta" => "meta " + ImportedInductionFunction,
            "partial" => "partial " + ImportedInductionFunction,
            "opaque" => "opaque recurse : Nat → Nat := fun n => n\n",
            "abbrev" => "abbrev recurse (n : Nat) : Nat := n\n",
            "theorem" => "theorem recurse : True := by trivial\n",
            _ => ImportedInductionFunction,
        };
        var dependency = ModuleWithReport("B", "namespace N\ndef seed : Nat := 1\n" + function
            + (boundary == "explicit" ? "theorem recurse.induct_unfolding : True := by trivial\n" : "")
            + "end N\n", "function source", declarations: ["N.recurse"], kind: "def");
        var other = boundary == "duplicate"
            ? ModuleWithReport("C", "namespace N\ndef seed : Nat := 1\n" + ImportedInductionFunction + "end N\n",
                "duplicate function", declarations: ["N.recurse"], kind: "def")
            : Module("C");
        var rootName = boundary == "private-root" ? "_private.D5.S0.Carrier.A.0.N.recurse.induct_unfolding"
            : boundary == "namespace" ? "Wrong.recurse.induct_unfolding"
            : boundary == "suffix" ? "N.recurse.invented_induction" : "N.recurse.induct_unfolding";
        var imported = boundary == "unimported" ? "import D5.S0.Carrier.C\n"
            : "import D5.S0.Carrier.B\nimport D5.S0.Carrier.C\n";
        var owner = ModuleWithReport("A", imported + "theorem a : True := by trivial\n",
            "old unbound induction", declarations: [rootName], kind: boundary == "kind" ? "def" : "theorem")
            with { Imports = boundary == "unimported" ? ["C"] : ["B", "C"] };
        var result = ValidateMathlibReanchor([owner, dependency, other],
            [owner with { StatementMaterial = "new unbound induction" }, dependency, other],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }
}
