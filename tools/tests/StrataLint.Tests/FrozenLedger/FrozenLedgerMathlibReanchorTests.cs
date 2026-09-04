using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void MathlibReanchorAllowsIncrementalReplacementWhenAllThreeConjunctsHold()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by\n  exact True.intro\n",
                    statementMaterial: "old elaborated True"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by\n  trivial\n",
                    statementMaterial: "new elaborated True"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsWeakenedTerminalTheorem()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : False := by\n  contradiction\n",
                    statementMaterial: "old elaborated False"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by\n  trivial\n",
                    statementMaterial: "new elaborated True"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsEnvironmentCommentLaundering()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by\n  exact True.intro\n",
                    statementMaterial: "old elaborated True"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by\n  trivial\n",
                    statementMaterial: "new elaborated True"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.CommentOnly);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsHiddenLocalDefinitionWeakening()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "def p : Prop := False\n\ntheorem a : p := by\n  contradiction\n",
                    statementMaterial: "old elaborated p"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "def p : Prop := True\n\ntheorem a : p := by\n  trivial\n",
                    statementMaterial: "new elaborated p"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsParenthesizedHiddenLocalDefinitionWeakening()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "def p : Prop := False\n\ntheorem a : (p) := by\n  contradiction\n",
                    statementMaterial: "old elaborated parenthesized p"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "def p : Prop := True\n\ntheorem a : (p) := by\n  trivial\n",
                    statementMaterial: "new elaborated parenthesized p"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsTightlySpacedHiddenLocalDefinitionWeakening()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "def p : Prop := 1 = 1\n\ntheorem a : p∧True := by simp [p]\n",
                    statementMaterial: "old elaborated conjunction"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "def p : Prop := True\n\ntheorem a : p∧True := by simp [p]\n",
                    statementMaterial: "new elaborated conjunction"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsIndentedAttributedHiddenDefinitionWeakening()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "  @[irreducible] def p : Prop := False\n\ntheorem a : p := by contradiction\n",
                    statementMaterial: "old elaborated p"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "  @[irreducible] def p : Prop := True\n\ntheorem a : p := by trivial\n",
                    statementMaterial: "new elaborated p"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorAllowsUnchangedTransitiveRepositoryDefinitionDependency()
    {
        var sharedModules = new[]
        {
            ModuleWithReport(
                "C",
                "def p : Prop := True\n",
                statementMaterial: "elaborated True",
                declarations: ["p"],
                kind: "def"),
            Module(
                "B",
                source: "import D5.S0.Carrier.C\ntheorem b : True := by trivial\n",
                imports: ["C"]),
        };
        var baseA = Module(
            "A",
            source: "import D5.S0.Carrier.B\ntheorem a : p := by exact True.intro\n",
            imports: ["B"]) with
        {
            StatementMaterial = "old elaborated p",
        };
        var candidateA = baseA with
        {
            Source = "import D5.S0.Carrier.B\ntheorem a : p := by trivial\n",
            StatementMaterial = "new elaborated p",
        };
        var result = ValidateMathlibReanchor(
            baseModules: sharedModules.Append(baseA).ToArray(),
            candidateModules: sharedModules.Append(candidateA).ToArray(),
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorAllowsEquationCompilerProofChange()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : ∀ x : Bool, x = x\n  | true => rfl\n  | false => rfl\n",
                    statementMaterial: "old elaborated reflexivity"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : ∀ x : Bool, x = x\n  | x => rfl\n",
                    statementMaterial: "new elaborated reflexivity"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsHiddenMutualDefinitionWeakening()
    {
        const string baseSource = """
            mutual
              @[irreducible] def p : Prop := False
              def q : Prop := p
            end
            theorem a : q := by contradiction
            """;
        const string candidateSource = """
            mutual
              @[irreducible] def p : Prop := True
              def q : Prop := p
            end
            theorem a : q := by trivial
            """;
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport("A", baseSource, statementMaterial: "old elaborated q"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport("A", candidateSource, statementMaterial: "new elaborated q"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsAmbientOpenResolutionChange()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "open External.Strong\ntheorem a : P := by trivial\n",
                    statementMaterial: "old elaborated External.Strong.P"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "open External.Weak\ntheorem a : P := by trivial\n",
                    statementMaterial: "new elaborated External.Weak.P"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsNonstandardAxiomClosure()
    {
        var baseModules = new[]
        {
            ModuleWithReport(
                "A",
                "theorem a : True := by\n  exact True.intro\n",
                statementMaterial: "old elaborated True"),
            Module("B"),
        };
        var candidateModules = new[]
        {
            ModuleWithReport(
                "A",
                "theorem a : True := by\n  trivial\n",
                statementMaterial: "new elaborated True"),
            Module("B"),
        };
        var baseCatalog = BuildCatalog(baseModules);
        var candidateCatalog = BuildCatalog(candidateModules);
        var candidateA = candidateCatalog.ByPath[RepoPathFor("A")];
        var authorizationCatalog = ReplaceCatalogMaterial(
            candidateCatalog,
            candidateA with { AxiomClosure = ["Nonstandard.axiom"] });

        var result = ValidateMathlibReanchorWithCatalogs(
            baseCatalog,
            authorizationCatalog,
            baseModules,
            candidateModules,
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade,
            candidateEventCatalog: candidateCatalog);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsReplacementSetWithUnchangedExtraModule()
    {
        var result = ValidateMathlibReanchor(
            baseModules: [Module("A"), Module("B", imports: ["A"])],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by trivial\n",
                    statementMaterial: "drifted A"),
                Module("B", imports: ["A"]),
            ],
            replacedModules: ["A", "B"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.Null(result.Recognition);
    }

    [Fact]
    public void MathlibReanchorRejectsReplacementSetThatOmitsDriftedModule()
    {
        var result = ValidateMathlibReanchor(
            baseModules: [Module("A"), Module("B")],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by trivial\n",
                    statementMaterial: "drifted A"),
                ModuleWithReport(
                    "B",
                    "theorem b : True := by trivial\n",
                    statementMaterial: "drifted B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.Null(result.Recognition);
    }

    [Fact]
    public void MathlibReanchorExtractorParseFailureFailsClosed()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by trivial\n",
                    statementMaterial: "old elaborated True"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : (True := by trivial\n",
                    statementMaterial: "new elaborated True"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorExtractorMacroDependencyFailsClosed()
    {
        const string baseSource = """
            macro "truthy" : term => `(True)
            theorem a : truthy := by
              exact True.intro
            """;
        const string candidateSource = """
            macro "truthy" : term => `(True)
            theorem a : truthy := by
              trivial
            """;
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    baseSource,
                    statementMaterial: "old elaborated truthy"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    candidateSource,
                    statementMaterial: "new elaborated truthy"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorExtractorImportedMacroDependencyFailsClosed()
    {
        var sharedMacroModule = Module(
            "B",
            source: "macro \"truthy\" : term => `(True)\ntheorem b : True := by trivial\n");
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "import D5.S0.Carrier.B\ntheorem a : truthy := by exact True.intro\n",
                    statementMaterial: "old elaborated truthy") with
                {
                    Imports = ["B"],
                },
                sharedMacroModule,
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "import D5.S0.Carrier.B\ntheorem a : truthy := by trivial\n",
                    statementMaterial: "new elaborated truthy") with
                {
                    Imports = ["B"],
                },
                sharedMacroModule,
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorExtractorUnresolvedRepositoryDependencyFailsClosed()
    {
        const string source =
            "theorem a : D5.S0.Carrier.Missing.p := by trivial\n";
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport("A", source, statementMaterial: "old elaborated missing p"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport("A", source + "\n", statementMaterial: "new elaborated missing p"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
    }

    private static MathlibReanchorResult ValidateMathlibReanchor(
        ModuleSpec[] baseModules,
        ModuleSpec[] candidateModules,
        string[] replacedModules,
        ReanchorEnvironment environment) =>
        ValidateMathlibReanchorWithCatalogs(
            BuildCatalog(baseModules),
            BuildCatalog(candidateModules),
            baseModules,
            candidateModules,
            replacedModules,
            environment);

    private static MathlibReanchorResult ValidateMathlibReanchorWithCatalogs(
        FrozenMaterialCatalog baseCatalog,
        FrozenMaterialCatalog candidateCatalog,
        IReadOnlyList<ModuleSpec> baseModules,
        IReadOnlyList<ModuleSpec> candidateModules,
        IReadOnlyCollection<string> replacedModules,
        ReanchorEnvironment environment,
        FrozenMaterialCatalog? candidateEventCatalog = null)
    {
        var baseEvents = EventFiles(baseCatalog);
        var eventCatalog = candidateEventCatalog ?? candidateCatalog;
        var candidateEventFiles = EventFiles(eventCatalog);
        var candidateEvents = replacedModules
            .Select(module => LedgerFileForModule(candidateEventFiles, module))
            .Concat(baseModules
                .Select(static module => module.Name)
                .Except(replacedModules, StringComparer.Ordinal)
                .Select(module => LedgerFileForModule(baseEvents, module)))
            .ToImmutableArray();
        var baseFiles = baseEvents
            .AddRange(ReanchorInputFiles(baseModules, environment, candidate: false));
        var currentFiles = candidateEvents
            .AddRange(ReanchorInputFiles(candidateModules, environment, candidate: true));
        var changes = RawChangeSet.CreateWithKinds(
            replacedModules
                .Select(module => (LedgerFileForModule(baseEvents, module).Path.Value, RawChangeKind.Deleted))
                .Concat(replacedModules.Select(module =>
                    (LedgerFileForModule(candidateEventFiles, module).Path.Value, RawChangeKind.Added)))
                .Concat(ChangedInputs(baseFiles, currentFiles)));
        var protectedBase = Snapshot(baseFiles);
        var current = Snapshot(currentFiles);
        var baseView = FrozenLedgerBaseViewReader.Read(protectedBase);
        var addedPaths = changes.Entries
            .Where(static change => change.Kind is RawChangeKind.Added)
            .Select(static change => change.Path)
            .ToImmutableHashSet();
        var deltaEvents = LoadEvents(candidateEvents)
            .Where(item => addedPaths.Contains(item.SourcePath))
            .ToImmutableArray();
        var recognition = FrozenLedgerIncrementalReplacementRecognition.Recognize(
            baseView,
            current,
            changes,
            deltaEvents,
            candidateCatalog);
        var authorization = new MathlibUpgradeFrozenLedgerReplacementAuthorization(
            protectedBase,
            current);
        var authorized = recognition is not null
            && authorization.IsAuthorized(new FrozenLedgerReplacementAuthorizationContext(
                recognition,
                baseView,
                candidateCatalog));
        return new MathlibReanchorResult(recognition, authorized);
    }

    private static ImmutableArray<RepositoryFile> ReanchorInputFiles(
        IReadOnlyList<ModuleSpec> modules,
        ReanchorEnvironment environment,
        bool candidate)
    {
        var upgraded = candidate && environment is ReanchorEnvironment.PinUpgrade;
        var lakefileComment = candidate && environment is ReanchorEnvironment.CommentOnly
            ? "-- candidate-only comment\n"
            : string.Empty;
        return modules.Select(module => TextFile(PathFor(module.Name), module.Source))
            .Append(TextFile(
                "lean-toolchain",
                upgraded
                    ? "leanprover/lean4:v4.25.0\n"
                    : "leanprover/lean4:v4.24.0\n"))
            .Append(TextFile("lakefile.lean", "import Lake\n" + lakefileComment))
            .Append(TextFile(
                "lake-manifest.json",
                MathlibManifest(upgraded ? new string('b', 40) : new string('a', 40))))
            .ToImmutableArray();
    }

    private static IEnumerable<(string Path, RawChangeKind Kind)> ChangedInputs(
        ImmutableArray<RepositoryFile> baseFiles,
        ImmutableArray<RepositoryFile> currentFiles)
    {
        var currentByPath = currentFiles.ToDictionary(static file => file.Path);
        foreach (var baseline in baseFiles.Where(static file =>
            !FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value)))
        {
            if (currentByPath.TryGetValue(baseline.Path, out var current)
                && !baseline.RawBytes.AsSpan().SequenceEqual(current.RawBytes.AsSpan()))
            {
                yield return (baseline.Path.Value, RawChangeKind.Modified);
            }
        }
    }

    private static RepositoryFile LedgerFileForModule(
        ImmutableArray<RepositoryFile> files,
        string module) =>
        files.Single(file => FrozenLedgerBaseViewReader.Read(Snapshot([file]))
            .ActiveByPath.ContainsKey(RepoPathFor(module)));

    private static RepositoryFile TextFile(string path, string text) => new(
        RepoPath.CreateKnown(path),
        ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text)),
        text);

    private static RepositorySnapshot Snapshot(IEnumerable<RepositoryFile> files) =>
        RepositorySnapshot.Create(files.ToImmutableDictionary(static file => file.Path));

    private static string MathlibManifest(string revision) =>
        JsonSerializer.Serialize(new
        {
            packages = new[]
            {
                new
                {
                    name = "mathlib",
                    type = "git",
                    url = "https://github.com/leanprover-community/mathlib4",
                    rev = revision,
                },
            },
        }) + "\n";

    private static FrozenMaterialCatalog ReplaceCatalogMaterial(
        FrozenMaterialCatalog catalog,
        FrozenNodeMaterial replacement) =>
        FrozenMaterialCatalog.Create(
            catalog.States,
            catalog.ClosedNodes
                .Where(material => material.RepoPath != replacement.RepoPath)
                .Append(replacement)
                .OrderBy(static material => material.RepoPath.Value, StringComparer.Ordinal)
                .ToImmutableArray(),
            catalog.OpenCases,
            catalog.TailRegistrations,
            catalog.Adjacency);

    private sealed record MathlibReanchorResult(
        FrozenLedgerIncrementalReplacementRecognition? Recognition,
        bool Authorized);

    private enum ReanchorEnvironment
    {
        PinUpgrade,
        CommentOnly,
    }

}
