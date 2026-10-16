using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("public section")]
    [InlineData("@[expose] public section")]
    [InlineData("@[expose] noncomputable section")]
    public void MathlibReanchorAcceptsModuleSectionProofChanges(string section)
    {
        var baseline = "module\npublic import Mathlib.Data.Nat.Basic\n"
            + section + "\nsection Inner\ntheorem a : True := by exact True.intro\nend Inner\nend\n";
        var candidate = baseline.Replace("exact True.intro", "trivial", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, statementMaterial: "old elaborated True"), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, statementMaterial: "new elaborated True"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("public section")]
    [InlineData("@[expose] public section")]
    public void MathlibReanchorRejectsModuleSectionDefinitionWeakening(string section)
    {
        var baseline = "module\n" + section
            + "\ndef p : Prop := False\ntheorem a : p := by contradiction\nend\n";
        var candidate = baseline.Replace("False", "True", StringComparison.Ordinal)
            .Replace("contradiction", "trivial", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, statementMaterial: "old elaborated p"), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, statementMaterial: "new elaborated p"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("public import")]
    [InlineData("meta import")]
    [InlineData("public meta import")]
    [InlineData("meta import all")]
    public void MathlibReanchorRejectsWeakeningThroughModuleImport(string import)
    {
        var source = "module\n" + import + " D5.S0.Carrier.B\ntheorem a : p := by trivial\n";
        var dependency = ModuleWithReport("B", "def p : Prop := False\n", "stable p",
            declarations: ["p"], kind: "def");
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", source, "old elaborated p") with { Imports = ["B"] }, dependency],
            candidateModules: [ModuleWithReport("A", source, "new elaborated p") with { Imports = ["B"] },
                dependency with { Source = "def p : Prop := True\n" }],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("public section")]
    [InlineData("@[expose] public section")]
    public void MathlibReanchorRejectsExtraModuleScopeTerminator(string section)
    {
        var source = "module\n" + section + "\ntheorem a : True := by trivial\nend\nend\n";
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", source, "old elaborated True"), Module("B")],
            candidateModules: [ModuleWithReport("A", source, "new elaborated True"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }
    [Theory]
    [InlineData("public ", false)]
    [InlineData("@[expose] public ", false)]
    [InlineData("public ", true)]
    [InlineData("@[expose] public ", true)]
    public void MathlibReanchorPreservesModuleDeclarationDependencies(string prefix, bool weaken)
    {
        var baseline = "module\n" + prefix + "def p : Prop := " + (weaken ? "False" : "True")
            + "\n" + prefix + "theorem a : p := by exact True.intro\n";
        var candidate = baseline.Replace("False", "True", StringComparison.Ordinal)
            .Replace("exact True.intro", "trivial", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, "old elaborated p"), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, "new elaborated p"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!weaken, result.Authorized);
    }

    [Theory]
    [InlineData("public import")]
    [InlineData("public meta import")]
    [InlineData("meta import all")]
    public void MathlibReanchorRejectsCustomSyntaxThroughTransitiveModuleImports(string import)
    {
        var source = "module\n" + import + " D5.S0.Carrier.B\ntheorem a : magic := by exact True.intro\n";
        var baseline = ModuleWithReport("A", source, "old elaborated magic") with { Imports = ["B"] };
        var candidate = baseline with
        {
            Source = source.Replace("exact True.intro", "trivial", StringComparison.Ordinal),
            StatementMaterial = "new elaborated magic",
        };
        var middle = Module("B", source: "module\npublic import D5.S0.Carrier.C\ntheorem b : True := by trivial\n",
            imports: ["C"]);
        var owner = Module("C", source: "notation \"magic\" => True\ntheorem c : True := by trivial\n");
        var result = ValidateMathlibReanchor(
            baseModules: [baseline, middle, owner], candidateModules: [candidate, middle, owner],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("scoped ", false)]
    [InlineData("@[reducible] scoped ", false)]
    [InlineData("scoped ", true)]
    [InlineData("@[reducible] scoped ", true)]
    public void MathlibReanchorPreservesScopedInstanceDomain(string prefix, bool changeDomain)
    {
        var baseline = "namespace N\nclass C where\n  carrier : Type\n"
            + prefix + "instance instC : C := ⟨Nat⟩\n"
            + "theorem a : ∀ x : @C.carrier instC, x = x := by intro x; rfl\nend N\n";
        var candidate = baseline.Replace("intro x; rfl", "intro x; exact rfl", StringComparison.Ordinal);
        if (changeDomain) candidate = candidate.Replace("⟨Nat⟩", "⟨Unit⟩", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, "old elaborated domain", declarations: ["N.a"]), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, "new elaborated domain", declarations: ["N.a"]), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeDomain, result.Authorized);
    }

    [Theory]
    [InlineData("namespace Outer.Inner", "end Inner\nend Outer", "Outer.Inner.a")]
    [InlineData("namespace Outer.Inner", "end Outer.Inner", "Outer.Inner.a")]
    [InlineData("section Outer.Inner", "end Inner\nend Outer", "a")]
    [InlineData("section Outer.Inner", "end Outer.Inner", "a")]
    public void MathlibReanchorAcceptsQualifiedScopeClosures(string scope, string close, string declaration)
    {
        var baseline = "module\n@[expose] public section\n" + scope
            + "\ntheorem a : True := by exact True.intro\n" + close + "\nend\n";
        var candidate = baseline.Replace("exact True.intro", "trivial", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, "old elaborated True", declarations: [declaration]), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, "new elaborated True", declarations: [declaration]), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesNamespaceAfterPartialClosure(bool changeDomain)
    {
        var baseline = "namespace Outer.Inner\ndef carrier : Type := Nat\nend Inner\n"
            + "theorem a : ∀ x : Inner.carrier, x = x := by intro x; rfl\nend Outer\n";
        var candidate = baseline.Replace("intro x; rfl", "intro x; exact rfl", StringComparison.Ordinal);
        if (changeDomain) candidate = candidate.Replace("Type := Nat", "Type := Unit", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, "old elaborated domain", declarations: ["Outer.a"]), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, "new elaborated domain", declarations: ["Outer.a"]), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeDomain, result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesAdjacentScopeCommands(bool changeDomain)
    {
        var baseline = "section\ndef carrier : Type := Nat\n"
            + "theorem a : ∀ x : carrier, x = x := by intro x; rfl\nend section\n";
        var candidate = baseline.Replace("intro x; rfl", "intro x; exact rfl", StringComparison.Ordinal);
        if (changeDomain) candidate = candidate.Replace("Type := Nat", "Type := Unit", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, "old elaborated domain"), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, "new elaborated domain"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeDomain, result.Authorized);
    }

    [Theory]
    [InlineData("nonrec ")]
    [InlineData("@[reducible] nonrec ")]
    [InlineData("private nonrec ")]
    public void MathlibReanchorRejectsChangedNonrecursiveDefinitionDomain(string prefix)
    {
        var baseline = prefix + "def carrier : Type := Nat\n"
            + "theorem a : ∀ x : carrier, x = x := by intro x; rfl\n";
        var candidate = baseline.Replace("Type := Nat", "Type := Unit", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, "old elaborated domain"), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, "new elaborated domain"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

}
