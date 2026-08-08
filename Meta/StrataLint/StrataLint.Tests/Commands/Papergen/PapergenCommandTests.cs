using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PapergenCommandTests
{
    private static readonly string RecipePath = PathFor("D5/P/D5-P001");
    private static readonly string FormalPath =
        PathFor("D5/S3/Zeros/CompletedZeta.xi_reading_reflection");
    private static readonly string BlueprintPath = PathFor("D5/B/S3/Zeros/CompletedZeta");

    private const string CanonicalRecipe = """
        blueprint:
          - D5/B/S3/Zeros/CompletedZeta
        decls:
          - D5/S3/Zeros/CompletedZeta.xi_reading_reflection
        evidence: []
        id: D5-P001
        narrative_order:
          - completed zeta
          - spectral reflection
        venue: arXiv-math.NT
        """ + "\n";

    [Theory]
    [InlineData("extra: value\n", "schema keys")]
    [InlineData("evidence: missing\n", "evidence must be a sequence")]
    [InlineData("narrative_order: []\n", "narrative_order must be a non-empty sequence")]
    [InlineData("venue: \"\"\n", "venue must be non-empty")]
    public void StrictSchemaRejectsMalformedRecipes(string replacement, string expected)
    {
        var recipe = replacement.StartsWith("extra:", StringComparison.Ordinal)
            ? CanonicalRecipe.Replace(
                "id: D5-P001\n",
                "extra: value\nid: D5-P001\n",
                StringComparison.Ordinal)
            : replacement.StartsWith("narrative_order:", StringComparison.Ordinal)
                ? CanonicalRecipe.Replace(
                    "narrative_order:\n  - completed zeta\n  - spectral reflection\n",
                    replacement,
                    StringComparison.Ordinal)
                : replacement.StartsWith("venue:", StringComparison.Ordinal)
                    ? CanonicalRecipe.Replace(
                        "venue: arXiv-math.NT\n",
                        replacement,
                        StringComparison.Ordinal)
                    : CanonicalRecipe.Replace(
                        "evidence: []\n",
                        replacement,
                        StringComparison.Ordinal);
        var bytes = CanonicalBytes(recipe);

        var result = PaperRecipeLoader.Load(bytes, "D5-P001.yaml");

        var invalid = Assert.IsType<PaperRecipeLoadOutcome.Invalid>(result);
        Assert.Contains(expected, invalid.Message, StringComparison.Ordinal);
    }

    public static TheoryData<byte[], string> NonCanonicalBytes => new()
    {
        { Encoding.UTF8.GetPreamble().Concat(Encoding.UTF8.GetBytes(CanonicalRecipe)).ToArray(), "BOM" },
        { Encoding.UTF8.GetBytes("id: D5-P001\n" + CanonicalRecipe.Replace("id: D5-P001\n", string.Empty, StringComparison.Ordinal)), "canonical bytes" },
        { Encoding.UTF8.GetBytes(CanonicalRecipe.TrimEnd('\n')), "canonical bytes" },
        { Encoding.UTF8.GetBytes(CanonicalRecipe.Replace("venue:", "venue: ", StringComparison.Ordinal)), "canonical bytes" },
        { Encoding.UTF8.GetBytes(CanonicalRecipe.Replace("venue: arXiv-math.NT\n", "venue: arXiv-math.NT \n", StringComparison.Ordinal)), "canonical bytes" },
        { Encoding.UTF8.GetBytes(CanonicalRecipe.Replace("\n", "\r\n", StringComparison.Ordinal)), "canonical bytes" },
        { [0xff, 0xfe], "UTF-8" },
    };

    [Theory]
    [MemberData(nameof(NonCanonicalBytes))]
    public void LoaderRejectsNonCanonicalRecipeBytes(byte[] bytes, string expected)
    {
        var result = PaperRecipeLoader.Load(ImmutableArray.CreateRange(bytes), "D5-P001.yaml");

        var invalid = Assert.IsType<PaperRecipeLoadOutcome.Invalid>(result);
        Assert.Contains(expected, invalid.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void LoaderRejectsFilenameIdMismatch()
    {
        var result = PaperRecipeLoader.Load(CanonicalBytes(CanonicalRecipe), "D5-P002.yaml");

        var invalid = Assert.IsType<PaperRecipeLoadOutcome.Invalid>(result);
        Assert.Contains("does not match filename", invalid.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("../D5-P001")]
    [InlineData("D5-P01")]
    [InlineData("D5-P001--frozen")]
    public void CommandRejectsNonCanonicalPaperIdBeforeFilesystemLookup(string id)
    {
        var result = PapergenCommand.Run("/repository-that-does-not-exist", TestGateway(), TestReportSource(), ["validate", id]);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(string.Empty, result.Output);
        Assert.Contains("paper id must be canonical A11", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("recipe file is missing", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("blueprint", "D5/S3/Zeros/CompletedZeta.xi_reading_reflection", "Blueprint GID")]
    [InlineData("decls", "D5/B/S3/Zeros/CompletedZeta", "formal declaration GID")]
    [InlineData("evidence", "D5/B/S3/Zeros/CompletedZeta", "Evidence GID")]
    public void LoaderRejectsGidsFromTheWrongPlane(string key, string gid, string expected)
    {
        var recipe = key switch
        {
            "blueprint" => CanonicalRecipe.Replace(
                "D5/B/S3/Zeros/CompletedZeta",
                gid,
                StringComparison.Ordinal),
            "decls" => CanonicalRecipe.Replace(
                "D5/S3/Zeros/CompletedZeta.xi_reading_reflection",
                gid,
                StringComparison.Ordinal),
            "evidence" => CanonicalRecipe.Replace(
                "evidence: []",
                $"evidence:\n  - {gid}",
                StringComparison.Ordinal),
            _ => throw new ArgumentOutOfRangeException(nameof(key)),
        };

        var result = PaperRecipeLoader.Load(CanonicalBytes(recipe), "D5-P001.yaml");

        var invalid = Assert.IsType<PaperRecipeLoadOutcome.Invalid>(result);
        Assert.Contains(expected, invalid.Message, StringComparison.Ordinal);
    }

    /// Target-file existence is checked across all three GID planes, not just declarations, so
    /// an implementation that iterates only recipe.Declarations cannot pass. Runs on a
    /// ledger-backed repository so it cannot be satisfied through the no-ledger path; the scanner
    /// half of the old test went with LeanDeclarationScanner's contract.
    [Theory]
    [InlineData("D5/S0/Carrier/A.lean")]
    [InlineData("Blueprint/D5/S0/Carrier/A.md")]
    [InlineData("Evidence/D5/S0/Carrier/A.result.json")]
    public void ValidatorRejectsRecipesWhoseTargetFileIsMissing(string missingRelativePath)
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A",
            evidenceGids: ["D5/E/S0/Carrier/A.result--json"]);
        var target = Path.Combine(repository.Path, missingRelativePath);
        Assert.True(File.Exists(target), $"fixture must create {missingRelativePath}");
        File.Delete(target);

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("target file is missing", invalid.Message, StringComparison.Ordinal);
    }

    /// The gateway refuses to validate the ledger's Git references. Membership must fail closed:
    /// an implementation that manufactures trust itself, or quietly falls back, stays green
    /// without this.
    [Fact]
    public void ValidatorFailsClosedWhenTheGatewayRefusesFrozenReferences()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.DenyingGateway,
            repository.Reports,
            "D5-P001");

        Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
    }

    [Fact]
    public void GoodRecipeValidatesAndCliEmitsAStableReceipt()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var firstConsole = new BufferedConsole();
        var secondConsole = new BufferedConsole();

        var validated = PaperRecipeValidator.Validate(repository.Path, repository.Gateway, repository.Reports, "D5-P001");
        var firstExit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.Gateway, repository.Reports),
            firstConsole);
        var secondExit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.Gateway, repository.Reports),
            secondConsole);

        var valid = Assert.IsType<PaperRecipeValidationOutcome.Valid>(validated);
        Assert.Equal("D5-P001", valid.Recipe.Id);
        Assert.Equal(0, firstExit);
        Assert.Equal(0, secondExit);
        Assert.Equal(firstConsole.Output, secondConsole.Output);
        Assert.Equal(string.Empty, firstConsole.Error);
        Assert.Equal(string.Empty, secondConsole.Error);
        // The receipt hash is compared against the recipe's real SHA-256, not just a 64-hex
        // shape: a constant would satisfy both the regex and the two-run equality check.
        var expectedHash = "sha256:" + Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(
            File.ReadAllBytes(Path.Combine(repository.Path, PathFor("D5/P/D5-P001")))));
        Assert.Contains($"recipe_sha256={expectedHash} ", firstConsole.Output, StringComparison.Ordinal);
        Assert.Matches(
            "^PAPERGEN_VALIDATE_OK id=D5-P001 gid=D5/P/D5-P001 "
            + "recipe_sha256=sha256:[0-9a-f]{64} decls=1 blueprint=1 evidence=0 "
            + "narrative_order=1 venue=arXiv-math.NT\\n$",
            firstConsole.Output);
    }

    /// A repository with no frozen ledger cannot certify anything. This is the fail-closed floor
    /// that forbids an optional-ledger fallback: without it, "keep the old behaviour when no
    /// ledger is present" would satisfy every other test in this class.
    [Fact]
    public void CliRejectsValidationWhenTheFrozenLedgerIsAbsent()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        Directory.Delete(
            Path.Combine(repository.Path, FrozenLedgerChangeClassifier.LedgerPath),
            recursive: true);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.Gateway, repository.Reports),
            console);

        Assert.Equal(1, exit);
        Assert.Equal(string.Empty, console.Output);
        Assert.Contains("PAPERGEN_VALIDATE_INVALID", console.Error, StringComparison.Ordinal);
        Assert.Contains(FrozenLedgerChangeClassifier.LedgerPath, console.Error, StringComparison.Ordinal);
    }

    /// The same floor at the validator boundary. Pinning it only through the CLI would leave the
    /// mutant where the command enforces a ledger while the validator keeps a no-ledger fallback
    /// to the source scanner.
    [Fact]
    public void ValidatorRejectsValidationWhenTheFrozenLedgerIsAbsent()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        Directory.Delete(
            Path.Combine(repository.Path, FrozenLedgerChangeClassifier.LedgerPath),
            recursive: true);

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains(FrozenLedgerChangeClassifier.LedgerPath, invalid.Message, StringComparison.Ordinal);
    }

    /// Reversed pairing of the mixed-recipe case. With only one ordering an implementation that
    /// inspects the last declaration, or lets a later entry overwrite an earlier verdict, stays
    /// green; the unfrozen entry is first here.
    [Fact]
    public void ValidatorRejectsMixedRecipesRegardlessOfDeclarationOrder()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/B.b", "D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A",
            unfrozen: ("B", "namespace D5.S0.Carrier.B\n\ntheorem b : True := by trivial\n\nend D5.S0.Carrier.B\n"));

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("D5/S0/Carrier/B.b", invalid.Message, StringComparison.Ordinal);
        Assert.Contains("not an active frozen declaration", invalid.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("D5/S0/Carrier/A.a", invalid.Message, StringComparison.Ordinal);
    }

    /// The unfrozen declaration shares its leaf name with the frozen one and differs only by
    /// module. Every other negative uses a distinct leaf name, so an implementation that flattens
    /// every active node's declaration ids and matches on the name alone -- never comparing
    /// RepoPath -- satisfies all of them; here it certifies a declaration that was never frozen.
    [Fact]
    public void ValidatorRejectsDeclarationsSharingALeafNameWithADifferentModule()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/B.a"],
            "D5/B/S0/Carrier/B",
            unfrozen: ("B", "namespace D5.S0.Carrier.B\n\ntheorem a : True := by trivial\n\nend D5.S0.Carrier.B\n"));

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("D5/S0/Carrier/B.a", invalid.Message, StringComparison.Ordinal);
        Assert.Contains("not an active frozen declaration", invalid.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("target file is missing", invalid.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("Lean declaration is missing", invalid.Message, StringComparison.Ordinal);
    }

    /// Membership must be read through the gateway's validated references. An implementation that
    /// calls TrustedFrozenGitReferences.CreateForTrustedAdapter itself never asks the gateway, and
    /// nothing else in the suite would notice.
    [Fact]
    public void ValidatorObtainsFrozenTrustThroughTheRepositoryGateway()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");

        PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        Assert.NotEqual(0, repository.Gateway.FrozenReferenceValidationCount);
    }

    /// A ledger that exists but does not parse must fail closed. Covering only the absent ledger
    /// would let a parse failure fall back to the source scanner, or to ad hoc scanning of the
    /// raw bytes, without any test noticing.
    [Fact]
    public void ValidatorRejectsValidationWhenTheFrozenLedgerIsMalformed()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var eventPath = Directory.EnumerateFiles(
            Path.Combine(repository.Path, FrozenLedgerChangeClassifier.LedgerPath)).First();
        File.WriteAllText(eventPath, "{\"not\": \"a ledger\"}\n", new UTF8Encoding(false));

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains(FrozenLedgerChangeClassifier.LedgerPath, invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LoaderRejectsEmptyDeclsWhileEmptyEvidenceStaysLegal()
    {
        var withoutDeclarations = CanonicalRecipe.Replace(
            "decls:\n  - D5/S3/Zeros/CompletedZeta.xi_reading_reflection\n",
            "decls: []\n",
            StringComparison.Ordinal);

        var empty = PaperRecipeLoader.Load(CanonicalBytes(withoutDeclarations), "D5-P001.yaml");
        var canonical = PaperRecipeLoader.Load(CanonicalBytes(CanonicalRecipe), "D5-P001.yaml");

        var invalid = Assert.IsType<PaperRecipeLoadOutcome.Invalid>(empty);
        Assert.Contains("decls must be a non-empty sequence", invalid.Message, StringComparison.Ordinal);
        foreach (var unrelated in (string[])["blueprint", "evidence", "narrative_order", "venue", "schema keys"])
        {
            Assert.DoesNotContain(unrelated, invalid.Message, StringComparison.Ordinal);
        }

        var loaded = Assert.IsType<PaperRecipeLoadOutcome.Loaded>(canonical);
        Assert.Empty(loaded.Recipe.Evidence);
        Assert.Single(loaded.Recipe.Declarations);
    }

    /// The ledger freezes carrier A only. The recipe names carrier B, whose module the ledger
    /// never froze at all.
    [Fact]
    public void ValidatorRejectsDeclarationsWhoseModuleIsNotActivelyFrozen()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/B.b"],
            "D5/B/S0/Carrier/B",
            unfrozen: ("B", "namespace D5.S0.Carrier.B\n\ntheorem b : True := by trivial\n\nend D5.S0.Carrier.B\n"));

        var outcome = PaperRecipeValidator.Validate(repository.Path, repository.Gateway, repository.Reports, "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("D5/S0/Carrier/B.b", invalid.Message, StringComparison.Ordinal);
        Assert.Contains("not an active frozen declaration", invalid.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("target file is missing", invalid.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("Lean declaration is missing", invalid.Message, StringComparison.Ordinal);
    }
}
