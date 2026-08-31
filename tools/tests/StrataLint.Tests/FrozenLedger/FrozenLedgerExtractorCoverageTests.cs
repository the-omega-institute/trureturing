using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void MathlibReanchorAcceptsShadowedTopLevelDeclarationWithForallBinder()
    {
        const string baseSource = """
            def n : Nat := 0
            theorem a : forall n : Nat, n = n := by
              intro value
              rfl
            """;
        const string candidateSource = """
            def n : Nat := 1
            theorem a : forall n : Nat, n = n := by
              simp
            """;

        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport("A", baseSource, statementMaterial: "old elaborated forall"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport("A", candidateSource, statementMaterial: "new elaborated forall"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorRejectsChangedFreeTopLevelDependency()
    {
        const string baseSource = """
            def n : Prop := False
            theorem a : n := by contradiction
            """;
        const string candidateSource = """
            def n : Prop := True
            theorem a : n := by trivial
            """;

        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport("A", baseSource, statementMaterial: "old elaborated n"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport("A", candidateSource, statementMaterial: "new elaborated n"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
        AssertReuseRejected(result.Failure);
    }

    [Fact]
    public void MathlibReanchorAcceptsExternalNameDespiteUnimportedRepositoryLeafCollision()
    {
        const string baseSource = """
            theorem a {X : Type} [Fintype X] : True := by
              exact True.intro
            """;
        const string candidateSource = """
            theorem a {X : Type} [Fintype X] : True := by
              trivial
            """;
        var collision = ModuleWithReport(
            "B",
            "def Fintype : Prop := True\n",
            statementMaterial: "repository leaf collision",
            declarations: ["Fintype"],
            kind: "def");

        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport("A", baseSource, statementMaterial: "old external Fintype"),
                collision,
            ],
            candidateModules:
            [
                ModuleWithReport("A", candidateSource, statementMaterial: "new external Fintype"),
                collision,
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorIgnoresChangedUnimportedRepositoryLeafCollision()
    {
        var baseline = ModuleWithReport(
            "A",
            "theorem a {X : Type} [Fintype X] : True := by exact True.intro\n",
            statementMaterial: "old external Fintype");
        var candidate = baseline with
        {
            Source = "theorem a {X : Type} [Fintype X] : True := by trivial\n",
            StatementMaterial = "new external Fintype",
        };
        var baseCollision = ModuleWithReport(
            "B",
            "def Fintype : Prop := True\n",
            statementMaterial: "stable repository collision",
            declarations: ["Fintype"],
            kind: "def");
        var candidateCollision = baseCollision with
        {
            Source = "def Fintype : Prop := False\n",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, baseCollision],
            candidateModules: [candidate, candidateCollision],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorAcceptsWhereFieldParameterShadowingTopLevelName()
    {
        const string baseSource = """
            structure End where
              toFun : Nat -> Nat
            def x : Nat := 0
            def a : End where
              toFun x := x
            """;
        const string candidateSource = """
            structure End where
              toFun : Nat -> Nat
            def x : Nat := 1
            def a : End where
              toFun x := x
            """;

        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport("A", baseSource, statementMaterial: "old End", kind: "def"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport("A", candidateSource, statementMaterial: "new End", kind: "def"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorAcceptsStructureFieldShadowingTopLevelName()
    {
        const string baseSource = """
            def kind : Nat := 0
            structure A where
              kind : Nat
            """;
        const string candidateSource = """
            def kind : Nat := 1
            structure A where
              kind : Nat
            """;

        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    baseSource,
                    statementMaterial: "old A",
                    declarations: ["A"],
                    kind: "structure"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    candidateSource,
                    statementMaterial: "new A",
                    declarations: ["A"],
                    kind: "structure"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorAcceptsPostfixUnitsTypeThroughItsImportedStemDeclaration()
    {
        var root = ModuleWithReport(
            "A",
            "import D5.S0.Carrier.B\ntheorem a : D5.S0.Carrier.GoldenIntˣ = D5.S0.Carrier.GoldenIntˣ := by exact rfl\n",
            statementMaterial: "elaborated units type") with { Imports = ["B"] };
        var dependency = ModuleWithReport(
            "B",
            "namespace D5.S0.Carrier\nstructure GoldenInt where\n  a : Int\nend D5.S0.Carrier\n",
            statementMaterial: "GoldenInt source",
            declarations: ["D5.S0.Carrier.GoldenInt"],
            kind: "structure");

        var result = ValidateMathlibReanchor(
            baseModules: [root, dependency],
            candidateModules:
            [
                root with
                {
                    Source = "import D5.S0.Carrier.B\ntheorem a : D5.S0.Carrier.GoldenIntˣ = D5.S0.Carrier.GoldenIntˣ := by rfl\n",
                    StatementMaterial = "re-elaborated units type",
                },
                dependency,
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorRejectsChangedImportedStemBehindPostfixUnitsType()
    {
        var baseRoot = ModuleWithReport(
            "A",
            "namespace D5.S0.Carrier\nstructure GoldenInt where\n  value : Int\ntheorem a : GoldenIntˣ = GoldenIntˣ := by exact rfl\nend D5.S0.Carrier\n",
            statementMaterial: "elaborated units type",
            declarations: ["D5.S0.Carrier.a"]);
        var candidateRoot = baseRoot with
        {
            Source = "namespace D5.S0.Carrier\nstructure GoldenInt where\n  value : Nat\ntheorem a : GoldenIntˣ = GoldenIntˣ := by rfl\nend D5.S0.Carrier\n",
            StatementMaterial = "re-elaborated units type",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseRoot, Module("B")],
            candidateModules: [candidateRoot, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
        AssertReuseRejected(result.Failure);
    }

    [Theory]
    [InlineData("structure A where\n  value : Nat\n", "inductive")]
    [InlineData("abbrev A := Nat\n", "def")]
    [InlineData("instance A : Inhabited Nat := ⟨0⟩\n", "def")]
    [InlineData("instance A : Nonempty Nat := ⟨0⟩\n", "theorem")]
    public void MathlibReanchorAcceptsInspectorKindForSourceDeclaration(
        string source,
        string inspectorKind)
    {
        var baseline = ModuleWithReport(
            "A",
            source,
            statementMaterial: "old elaborated declaration",
            declarations: ["A"],
            kind: inspectorKind);
        var candidate = baseline with
        {
            Source = "-- candidate pin\n" + source,
            StatementMaterial = "new elaborated declaration",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorRejectsUnrelatedInspectorKindForSourceDeclaration()
    {
        var baseline = ModuleWithReport(
            "A",
            "structure A where\n  value : Nat\n",
            statementMaterial: "old elaborated declaration",
            declarations: ["A"],
            kind: "theorem");
        var candidate = baseline with
        {
            Source = "-- candidate pin\n" + baseline.Source,
            StatementMaterial = "new elaborated declaration",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
        AssertReuseRejected(result.Failure);
    }

    [Fact]
    public void MathlibReanchorAcceptsUtf8LengthPrefixedDeclarationNameKey()
    {
        var baseline = ModuleWithReport(
            "A",
            "theorem eval₂ : True := by exact True.intro\n",
            statementMaterial: "old elaborated Unicode declaration",
            declarations: ["eval₂"]);
        var candidate = baseline with
        {
            Source = "theorem eval₂ : True := by trivial\n",
            StatementMaterial = "new elaborated Unicode declaration",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorIgnoresLocalNotationFromImportedModule()
    {
        var notationOwner = Module(
            "B",
            source: "local notation \"p\" => True\ntheorem b : True := by trivial\n");
        var baseline = ModuleWithReport(
            "A",
            "import D5.S0.Carrier.B\ntheorem a (p : Prop) : p -> p := by exact fun h => h\n",
            statementMaterial: "old elaborated implication") with { Imports = ["B"] };
        var candidate = baseline with
        {
            Source = "import D5.S0.Carrier.B\ntheorem a (p : Prop) : p -> p := by\n  intro h\n  exact h\n",
            StatementMaterial = "new elaborated implication",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, notationOwner],
            candidateModules: [candidate, notationOwner],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorFingerprintsSameModuleLocalNotationSource()
    {
        var baseline = ModuleWithReport(
            "A",
            "local notation \"truthy\" => True\ntheorem a : truthy := by exact True.intro\n",
            statementMaterial: "old elaborated local notation");
        var candidate = baseline with
        {
            Source = "local notation \"truthy\" => True\ntheorem a : truthy := by trivial\n",
            StatementMaterial = "new elaborated local notation",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorRejectsChangedSameModuleLocalNotationSource()
    {
        var baseline = ModuleWithReport(
            "A",
            "local notation \"truthy\" => True\ntheorem a : truthy := by trivial\n",
            statementMaterial: "old elaborated local notation");
        var candidate = baseline with
        {
            Source = "local notation \"truthy\" => False\ntheorem a : truthy := by contradiction\n",
            StatementMaterial = "new elaborated local notation",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
        AssertReuseRejected(result.Failure);
    }

    [Theory]
    [InlineData(
        "local instance (p : Prop) : Decidable p := Classical.propDecidable p\ntheorem a : True := by exact True.intro\n",
        "instDecidable_d5",
        "def")]
    [InlineData(
        "inductive A | mk deriving Repr\ntheorem a : True := by exact True.intro\n",
        "instReprA",
        "def")]
    [InlineData(
        "theorem a : True := by exact True.intro\n",
        "congr_simp",
        "theorem")]
    [InlineData(
        "theorem a : True := by exact True.intro\n",
        "term_.support",
        "def")]
    [InlineData(
        "theorem a : True := by exact True.intro\n",
        "_aux_A___macroRules__private_A_0_A_termA.sum_1",
        "def")]
    public void MathlibReanchorUsesSourceClosureForCompilerGeneratedDeclaration(
        string source,
        string generatedName,
        string generatedKind)
    {
        var baseline = ModuleWithReport(
            "A",
            source,
            statementMaterial: "old generated declaration",
            declarations: [generatedName],
            kind: generatedKind);
        var candidate = baseline with
        {
            Source = source.Replace("exact True.intro", "trivial", StringComparison.Ordinal),
            StatementMaterial = "new generated declaration",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorRejectsChangedAnonymousInstanceGeneratorSource()
    {
        var baseline = ModuleWithReport(
            "A",
            "local instance (p : Prop) : Decidable p := Classical.propDecidable p\ntheorem a : True := by trivial\n",
            statementMaterial: "old generated declaration",
            declarations: ["instDecidable_d5"],
            kind: "def");
        var candidate = baseline with
        {
            Source = "local instance (p : Prop) : Decidable p := inferInstance\ntheorem a : True := by trivial\n",
            StatementMaterial = "new generated declaration",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
        AssertReuseRejected(result.Failure);
    }

    [Fact]
    public void MathlibReanchorIgnoresCompilerGeneratedDeclarationNameDrift()
    {
        var baseline = ModuleWithReport(
            "A",
            "local instance (p : Prop) : Decidable p := Classical.propDecidable p\n",
            statementMaterial: "old generated declaration",
            declarations: ["instDecidable_d5"],
            kind: "def");
        var candidate = baseline with
        {
            Source = "-- compiler pin changed\n" + baseline.Source,
            StatementMaterial = "new generated declaration",
            Declarations = ["instDecidable_d6"],
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorIgnoresCompilerGeneratedDeclarationCountDrift()
    {
        var baseline = ModuleWithReport(
            "A",
            "inductive A | mk deriving Repr\n",
            statementMaterial: "old generated declarations",
            declarations: ["instReprA"],
            kind: "def");
        var candidate = baseline with
        {
            Source = "-- compiler pin changed\n" + baseline.Source,
            StatementMaterial = "new generated declarations",
            Declarations = ["instReprA", "term_.support"],
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorIgnoresTopLevelExampleProofChanges()
    {
        var baseline = ModuleWithReport(
            "A",
            "def a : Nat := 0\nexample : True := by exact True.intro\n",
            statementMaterial: "old elaborated a",
            declarations: ["a"],
            kind: "def");
        var candidate = baseline with
        {
            Source = "def a : Nat := 0\nexample : True := by trivial\n",
            StatementMaterial = "new elaborated a",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorStillRejectsDefinitionChangeBeforeTopLevelExample()
    {
        var baseline = ModuleWithReport(
            "A",
            "def a : Nat := 0\nexample : True := by trivial\n",
            statementMaterial: "old elaborated a",
            declarations: ["a"],
            kind: "def");
        var candidate = baseline with
        {
            Source = "def a : Nat := 1\nexample : True := by exact True.intro\n",
            StatementMaterial = "new elaborated a",
        };

        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")],
            candidateModules: [candidate, Module("B")],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
        AssertReuseRejected(result.Failure);
    }
}
