using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData(false, "g'")]
    [InlineData(true, "g'")]
    [InlineData(false, "a'")]
    [InlineData(true, "a'")]
    public void EqualityAmbiguityRejectsChangedDependency(bool spaced, string name)
    {
        var source = FirstOrderEqualitySource(spaced, name);
        AssertIdentifierReanchor(source, source.Replace(".inl 0", ".inl 1", StringComparison.Ordinal),
            [], [], expected: false);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void EqualityAmbiguityAllowsUnchangedOrProofOnlySource(bool spaced, bool proofOnly)
    {
        var source = FirstOrderEqualitySource(spaced, "g'");
        var after = proofOnly ? source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal) : source;
        AssertIdentifierReanchor(source, after, [], [], expected: true);
    }

    [Theory]
    [InlineData(false, "g'")]
    [InlineData(true, "g'")]
    [InlineData(false, "a'")]
    [InlineData(true, "a'")]
    public void EqualityAmbiguityPreservesBoundNameShadowing(bool spaced, string name)
    {
        var source = FirstOrderEqualitySource(spaced, name).Replace("(t :", $"(t {name} :", StringComparison.Ordinal);
        AssertIdentifierReanchor(source, source.Replace(".inl 0", ".inl 1", StringComparison.Ordinal),
            [], [], expected: true);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualityAmbiguityAllowsRealCharacterProofChangeAndRejectsLiteralChange(bool spaced)
    {
        var source = "def unrelated : Nat := 0\n"
            + $"theorem a : 'g' ={(spaced ? " " : "")}'g' := by rfl\n";
        AssertIdentifierReanchor(source, source, [], [], expected: true);
        AssertIdentifierReanchor(source, source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal),
            [], [], expected: true);
        AssertIdentifierReanchor(source, source.Replace(":= 0", ":= 1", StringComparison.Ordinal),
            [], [], expected: true);
        AssertIdentifierReanchor(source, source.Replace("'g'", "'a'", StringComparison.Ordinal),
            [], [], expected: false);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualityContextWhitespacePreservesReanchorInBothDirections(bool spacedBefore)
    {
        AssertIdentifierReanchor(FirstOrderEqualitySource(spacedBefore, "g'"),
            FirstOrderEqualitySource(!spacedBefore, "g'"), [], [], expected: true);
    }

    [Theory]
    [InlineData(false, false, "g'")]
    [InlineData(false, true, "g'")]
    [InlineData(true, false, "g'")]
    [InlineData(true, true, "g'")]
    [InlineData(false, false, "other")]
    [InlineData(false, true, "other")]
    [InlineData(true, false, "other")]
    [InlineData(true, true, "other")]
    public void EqualityContextCharactersIgnoreDefinitionChanges(bool spaced, bool imported, string name)
    {
        var proposition = $"theorem a : 'g' ={(spaced ? " " : "")}'g' := by rfl\n";
        var source = imported ? "import D5.S0.Carrier.Helper\n" + proposition
            : $"def {name} : Nat := 0\n" + proposition;
        var before = imported ? new[] { IdentifierHelper(name, "0") } : [];
        var after = imported ? new[] { IdentifierHelper(name, "1") } : [];
        AssertIdentifierReanchor(source, source, before, before, expected: true);
        AssertIdentifierReanchor(source, source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal),
            before, before, expected: true);
        AssertIdentifierReanchor(source, source.Replace(":= 0", ":= 1", StringComparison.Ordinal),
            before, after, expected: true);
        AssertIdentifierReanchor(source, source.Replace("'g'", "'a'", StringComparison.Ordinal),
            before, before, expected: false);
    }

    [Theory]
    [InlineData(false, "g'")]
    [InlineData(true, "g'")]
    [InlineData(false, "a'")]
    [InlineData(true, "a'")]
    public void EqualityContextRetainsImportedFirstOrderDependencies(bool spaced, string name)
    {
        var helperSource = "import Mathlib.ModelTheory.Syntax\nnamespace D5.S0.Carrier.Helper\n"
            + $"def {name} : FirstOrder.Language.Term FirstOrder.Language.empty (Sum Nat (Fin 0)) := .var (.inl 0)\n"
            + "end D5.S0.Carrier.Helper\n";
        var helper = ModuleWithReport("Helper", helperSource, statementMaterial: "Term", declarations: [name], kind: "def");
        var changed = helper with { Source = helperSource.Replace(".inl 0", ".inl 1", StringComparison.Ordinal) };
        var source = "import D5.S0.Carrier.Helper\nopen scoped FirstOrder\nopen D5.S0.Carrier.Helper\n"
            + "theorem a (t : FirstOrder.Language.Term FirstOrder.Language.empty (Sum Nat (Fin 0))) :\n"
            + $"    (t ='{(spaced ? " " : "")}{name}) = (t ='{(spaced ? " " : "")}{name}) := by rfl\n";
        AssertIdentifierReanchor(source, source, [helper], [helper], expected: true);
        AssertIdentifierReanchor(source, source, [helper], [changed], expected: false);
    }

    [Theory]
    [InlineData("namespace FirstOrder\n", "end FirstOrder\n")]
    [InlineData("section Local\nopen scoped FirstOrder\n", "end Local\n")]
    [InlineData("open scoped FirstOrder in\n", "")]
    public void EqualityContextScopeRestorationKeepsCharacterDependenciesInert(string prefix, string suffix)
    {
        var source = "import Mathlib.ModelTheory.Syntax\ndef g' : Nat := 0\n"
            + prefix + "example (t g' : FirstOrder.Language.Term FirstOrder.Language.empty (Sum Nat (Fin 0))) :\n"
            + "    (t ='g') = (t =' g') := by rfl\n" + suffix
            + "theorem a : 'g' ='g' := by rfl\n";
        AssertIdentifierReanchor(source, source.Replace(":= 0", ":= 1", StringComparison.Ordinal), [], [], expected: true);
    }

    private static string FirstOrderEqualitySource(bool spaced, string name) =>
        "import Mathlib.ModelTheory.Syntax\nopen scoped FirstOrder\n"
        + $"def {name} : FirstOrder.Language.Term FirstOrder.Language.empty (Sum Nat (Fin 0)) := .var (.inl 0)\n"
        + "theorem a (t : FirstOrder.Language.Term FirstOrder.Language.empty (Sum Nat (Fin 0))) :\n"
        + $"    (t ='{(spaced ? " " : "")}{name}) = (t ='{(spaced ? " " : "")}{name}) := by rfl\n";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorRejectsChangedDependencyBesideDependentComposition(bool spaced)
    {
        var source = DependentCompositionSource(spaced);
        AssertIdentifierReanchor(source, source.Replace("=> 0", "=> 1", StringComparison.Ordinal), [], [], expected: false);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void MathlibReanchorAllowsDependentCompositionWithUnchangedOrProofOnlySource(bool spaced, bool proofOnly)
    {
        var source = DependentCompositionSource(spaced);
        var after = proofOnly ? source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal) : source;
        AssertIdentifierReanchor(source, after, [], [], expected: true);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorDoesNotResolveDependentCompositionShadowedBinder(bool spaced)
    {
        var source = DependentCompositionSource(spaced).Replace("(f :", "(f g' :", StringComparison.Ordinal);
        AssertIdentifierReanchor(source, source.Replace("=> 0", "=> 1", StringComparison.Ordinal), [], [], expected: true);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DependentCompositionPreservesUnchangedImportAdjacencyAndPropositionSource(bool spaced)
    {
        var helper = Module("Helper", source: DependentCompositionSource(spaced));
        const string consumer = "import D5.S0.Carrier.Helper\ntheorem a : True := by trivial\n";
        var adjacency = LeanImportAdjacency.BuildFromSources(Snapshot([
            TextFile(PathFor("Helper"), helper.Source), TextFile(PathFor("A"), consumer)]));
        Assert.Equal(RepoPathFor("Helper"), Assert.Single(adjacency[RepoPathFor("A")]));
        Assert.Empty(adjacency[RepoPathFor("Helper")]);
        AssertIdentifierReanchor(consumer, consumer.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
            [helper], [helper], expected: true);
    }

    [Fact]
    public void MathlibReanchorPreservesDependentCompositionWhitespace()
    {
        AssertIdentifierReanchor(DependentCompositionSource(spaced: true), DependentCompositionSource(spaced: false),
            [], [], expected: true);
    }

    private static string DependentCompositionSource(bool spaced) =>
        "import Mathlib.Logic.Function.Defs\ndef g' : Nat -> Nat := fun _ => 0\n"
        + $"theorem a (f : Nat -> Nat) : (f \u2218'{(spaced ? " " : "")}g') = (f \u2218'{(spaced ? " " : "")}g') := by rfl\n";

    [Theory]
    [InlineData("p", "p")]
    [InlineData("p?", "p?")]
    [InlineData("p!", "p!")]
    [InlineData("\u00abp?\u00bb", "p?")]
    [InlineData("p!", "\u00abp!\u00bb")]
    [InlineData("p\u2127", "p\u2127")]
    [InlineData("p\U0001d49c", "p\U0001d49c")]
    [InlineData("p\u2080", "p\u2080")]
    [InlineData("\u00abby\u00bb", "\u00abby\u00bb")]
    public void MathlibReanchorRejectsChangedLocalIdentifierDependency(string declaration, string reference)
    {
        var before = $"def {declaration} : Prop := 1 = 1\ntheorem a : {reference} := by rfl\n";
        var after = $"def {declaration} : Prop := True\ntheorem a : {reference} := by trivial\n";
        AssertIdentifierReanchor(before, after, [], [], expected: false);
    }

    [Theory]
    [InlineData("p", "p")]
    [InlineData("p?", "p?")]
    [InlineData("p!", "p!")]
    [InlineData("\u00abp?\u00bb", "p?")]
    [InlineData("p!", "\u00abp!\u00bb")]
    [InlineData("p\u2127", "p\u2127")]
    [InlineData("p\U0001d49c", "p\U0001d49c")]
    [InlineData("p\u2080", "p\u2080")]
    [InlineData("\u00abby\u00bb", "\u00abby\u00bb")]
    public void MathlibReanchorAllowsUnchangedLocalIdentifierDependencyAndProofChange(string declaration, string reference)
    {
        var source = $"def {declaration} : Prop := 1 = 1\ntheorem a : {reference} := by rfl\n";
        AssertIdentifierReanchor(source, source, [], [], expected: true);
        AssertIdentifierReanchor(source, source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal), [], [], expected: true);
    }

    [Theory]
    [InlineData("probe", "probe")]
    [InlineData("probe?", "probe?")]
    [InlineData("probe!", "probe!")]
    [InlineData("\u00abprobe?\u00bb", "probe?")]
    [InlineData("probe!", "\u00abprobe!\u00bb")]
    [InlineData("\U0001d49c", "\U0001d49c")]
    [InlineData("\u00abprobe.dot?\u00bb", "\u00abprobe.dot?\u00bb")]
    [InlineData("\u00abprobe space!\u00bb", "\u00abprobe space!\u00bb")]
    public void MathlibReanchorRejectsChangedImportedIdentifierDependency(string declaration, string reference)
    {
        var helper = IdentifierHelper(declaration, "0");
        var changed = IdentifierHelper(declaration, "1");
        var consumer = IdentifierConsumer(reference);
        AssertIdentifierReanchor(consumer, consumer, [helper], [changed], expected: false);
    }

    [Theory]
    [InlineData("probe", "probe")]
    [InlineData("probe?", "probe?")]
    [InlineData("probe!", "probe!")]
    [InlineData("\u00abprobe?\u00bb", "probe?")]
    [InlineData("probe!", "\u00abprobe!\u00bb")]
    [InlineData("\U0001d49c", "\U0001d49c")]
    [InlineData("\u00abprobe.dot?\u00bb", "\u00abprobe.dot?\u00bb")]
    [InlineData("\u00abprobe space!\u00bb", "\u00abprobe space!\u00bb")]
    public void MathlibReanchorAllowsUnchangedImportedIdentifierDependencyAndProofChange(string declaration, string reference)
    {
        var helper = IdentifierHelper(declaration, "0");
        var consumer = IdentifierConsumer(reference);
        AssertIdentifierReanchor(consumer, consumer, [helper], [helper], expected: true);
        AssertIdentifierReanchor(consumer, consumer.Replace("by rfl", "by exact rfl", StringComparison.Ordinal), [helper], [helper], expected: true);
    }

    [Theory]
    [InlineData("probe?")]
    [InlineData("probe!")]
    [InlineData("\u00abprobe?\u00bb")]
    [InlineData("\U0001d49c")]
    public void MathlibReanchorRejectsUnresolvedQualifiedIdentifierDependency(string reference)
    {
        var consumer = IdentifierConsumer(reference);
        AssertIdentifierReanchor(consumer, consumer, [Module("Helper")], [Module("Helper")], expected: false);
    }

    [Theory]
    [InlineData("\u2211'")]
    [InlineData("\u220f'")]
    public void MathlibReanchorAllowsPrimeNotationInUnchangedImportedSource(string notation)
    {
        var helper = Module("Helper", source:
            "import Mathlib.Topology.Algebra.InfiniteSum.Defs\n"
            + $"theorem helper (f : Nat -> Nat) : ({notation} n, f n) = ({notation} n, f n) := by rfl\n");
        const string consumer = "import D5.S0.Carrier.Helper\ntheorem a : True := by trivial\n";
        AssertIdentifierReanchor(consumer, consumer.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal), [helper], [helper], expected: true);
    }

    [Theory]
    [InlineData("\u2211'")]
    [InlineData("\u220f'")]
    public void PrimeNotationPreservesSourceImportAdjacency(string notation)
    {
        var helper = TextFile(PathFor("Helper"), "def probe : Nat := 0\n");
        var consumer = TextFile(PathFor("A"), "import D5.S0.Carrier.Helper\n"
            + "import Mathlib.Topology.Algebra.InfiniteSum.Defs\n"
            + $"theorem a (f : Nat -> Nat) : ({notation} n, f n) = ({notation} n, f n) := by rfl\n");
        var adjacency = LeanImportAdjacency.BuildFromSources(Snapshot([helper, consumer]));
        Assert.Equal(RepoPathFor("Helper"), Assert.Single(adjacency[RepoPathFor("A")]));
        Assert.Empty(adjacency[RepoPathFor("Helper")]);
    }

    [Theory]
    [InlineData("\u2211'")]
    [InlineData("\u220f'")]
    public void MathlibReanchorDoesNotResolvePrimedBinderAsDefinitionDependency(string notation)
    {
        var source = "import Mathlib.Topology.Algebra.InfiniteSum.Defs\ndef n : Nat := 0\n"
            + $"theorem a (f : Nat -> Nat) : ({notation} n, f n) = ({notation} n, f n) := by rfl\n";
        AssertIdentifierReanchor(source, source.Replace(":= 0", ":= 1", StringComparison.Ordinal), [], [], expected: true);
    }

    [Theory]
    [InlineData("a?", "a?")]
    [InlineData("a!", "a!")]
    [InlineData("\u00aba?\u00bb", "a?")]
    [InlineData("\U0001d49c", "\U0001d49c")]
    [InlineData("\u00aba.dot?\u00bb", "a.dot?")]
    public void MathlibReanchorResolvesIdentifierDeclarationNames(string spelling, string name)
    {
        var before = ModuleWithReport("A", $"theorem {spelling} : True := by trivial\n",
            statementMaterial: "old True", declarations: [name]);
        var after = before with
        {
            Source = $"theorem {spelling} : True := by exact True.intro\n",
            StatementMaterial = "new True",
        };
        var result = ValidateMathlibReanchor([before], [after], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("p?")]
    [InlineData("p!")]
    [InlineData("\u00abp?\u00bb")]
    [InlineData("\U0001d49c")]
    [InlineData("\u00abby\u00bb")]
    public void MathlibReanchorDoesNotResolveBoundIdentifierAsDefinitionDependency(string name)
    {
        var source = $"def {name} : Nat := 0\ntheorem a ({name} : Nat) : {name} = {name} := by rfl\n";
        AssertIdentifierReanchor(source, source.Replace(":= 0", ":= 1", StringComparison.Ordinal), [], [], expected: true);
    }

    [Fact]
    public void MathlibReanchorAllowsImageNotationInUnchangedImportedSource()
    {
        var helper = Module("Helper", source: "import Mathlib.Data.Set.Image\n"
            + "theorem helper (f : Nat -> Nat) (s : Set Nat) : f '' s = f '' s := rfl\n");
        const string consumer = "import D5.S0.Carrier.Helper\ntheorem a : True := by trivial\n";
        AssertIdentifierReanchor(consumer, consumer, [helper], [helper], expected: true);
        AssertIdentifierReanchor(consumer, consumer.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
            [helper], [helper], expected: true);
    }

    [Fact]
    public void ImageNotationPreservesSourceImportAdjacency()
    {
        var helper = TextFile(PathFor("Helper"), "import Mathlib.Data.Set.Image\n"
            + "theorem helper (f : Nat -> Nat) (s : Set Nat) : f '' s = f '' s := rfl\n");
        var consumer = TextFile(PathFor("A"), "import D5.S0.Carrier.Helper\ntheorem a : True := by trivial\n");
        var adjacency = LeanImportAdjacency.BuildFromSources(Snapshot([helper, consumer]));
        Assert.Equal(RepoPathFor("Helper"), Assert.Single(adjacency[RepoPathFor("A")]));
        Assert.Empty(adjacency[RepoPathFor("Helper")]);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorAllowsImageNotationWithUnchangedOrProofOnlySource(bool proofOnly)
    {
        const string source = "import Mathlib.Data.Set.Image\n"
            + "theorem a (f : Nat -> Nat) (s : Set Nat) : f '' s = f '' s := by rfl\n";
        var after = proofOnly ? source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal) : source;
        AssertIdentifierReanchor(source, after, [], [], expected: true);
    }

    [Theory]
    [InlineData("\u2211'", false)]
    [InlineData("\u220f'", false)]
    [InlineData("\u2211'", true)]
    [InlineData("\u220f'", true)]
    public void MathlibReanchorDoesNotResolveAdjacentPrimedBinderAsDefinitionDependency(string notation, bool spaced)
    {
        var source = PrimedBinderSource(notation, spaced);
        AssertIdentifierReanchor(source, source.Replace(":= 0", ":= 1", StringComparison.Ordinal), [], [], expected: true);
    }

    [Theory]
    [InlineData("\u2211'")]
    [InlineData("\u220f'")]
    public void MathlibReanchorPreservesPrimeBinderWhitespace(string notation)
    {
        AssertIdentifierReanchor(PrimedBinderSource(notation, spaced: true), PrimedBinderSource(notation, spaced: false),
            [], [], expected: true);
    }

    [Theory]
    [InlineData("\u2211'", false)]
    [InlineData("\u220f'", false)]
    [InlineData("\u2211'", true)]
    [InlineData("\u220f'", true)]
    public void MathlibReanchorAllowsPrimedBinderWithUnchangedDefinitionAndProofChange(string notation, bool spaced)
    {
        var source = PrimedBinderSource(notation, spaced);
        AssertIdentifierReanchor(source, source, [], [], expected: true);
        AssertIdentifierReanchor(source, source.Replace("by rfl", "by exact rfl", StringComparison.Ordinal), [], [], expected: true);
    }

    [Theory]
    [InlineData("\u2211'", false)]
    [InlineData("\u220f'", false)]
    [InlineData("\u2211'", true)]
    [InlineData("\u220f'", true)]
    public void MathlibReanchorRejectsChangedDependencyBesidePrimedBinder(string notation, bool spaced)
    {
        var source = PrimedBinderSource(notation, spaced)
            .Replace("def n'", "def offset : Nat := 0\ndef n'", StringComparison.Ordinal)
            .Replace("f n')", "f n') + offset", StringComparison.Ordinal);
        AssertIdentifierReanchor(source, source.Replace("offset : Nat := 0", "offset : Nat := 1", StringComparison.Ordinal),
            [], [], expected: false);
    }

    private static string PrimedBinderSource(string notation, bool spaced)
    {
        var term = $"({notation}{(spaced ? " " : string.Empty)}n', f n')";
        return "import Mathlib.Topology.Algebra.InfiniteSum.Defs\ndef n' : Nat := 0\n"
            + $"theorem a (f : Nat -> Nat) : {term} = {term} := by rfl\n";
    }

    private static ModuleSpec IdentifierHelper(string declaration, string body) =>
        ModuleWithReport("Helper", $"namespace D5.S0.Carrier.Helper\ndef {declaration} : Nat := {body}\nend D5.S0.Carrier.Helper\n",
            statementMaterial: "Nat", declarations: [declaration.Trim('\u00ab', '\u00bb')], kind: "def");

    private static string IdentifierConsumer(string reference) =>
        "import D5.S0.Carrier.Helper\n"
        + $"theorem a : D5.S0.Carrier.Helper.{reference} = D5.S0.Carrier.Helper.{reference} := by rfl\n";

    private static void AssertIdentifierReanchor(string before, string after,
        ModuleSpec[] baseDependencies, ModuleSpec[] candidateDependencies, bool expected)
    {
        var baseRoot = ModuleWithReport("A", before, statementMaterial: "old elaborated statement") with
        {
            Imports = baseDependencies.Select(static module => module.Name).ToArray(),
        };
        var candidateRoot = baseRoot with { Source = after, StatementMaterial = "new elaborated statement" };
        var result = ValidateMathlibReanchor(
            baseModules: [..baseDependencies, baseRoot],
            candidateModules: [..candidateDependencies, candidateRoot],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);
        Assert.NotNull(result.Recognition);
        Assert.Equal(expected, result.Authorized);
    }
}
