using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PapergenCommandTests
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
        var result = PapergenCommand.Run("/repository-that-does-not-exist", ["validate", id]);

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

    [Fact]
    public void ValidatorRejectsMissingFilesAndLeanDeclarations()
    {
        using var repository = RecipeRepository();
        var missingFile = PaperRecipeValidator.Validate(repository.Path, "D5-P001");
        File.WriteAllText(
            Path.Combine(repository.Path, FormalPath),
            "namespace D5\n\nend D5\n");
        File.WriteAllText(
            Path.Combine(repository.Path, BlueprintPath),
            "# Completed Zeta\n");
        var missingDeclaration = PaperRecipeValidator.Validate(repository.Path, "D5-P001");

        Assert.Contains("target file is missing", Assert.IsType<PaperRecipeValidationOutcome.Invalid>(missingFile).Message);
        Assert.Contains("Lean declaration is missing", Assert.IsType<PaperRecipeValidationOutcome.Invalid>(missingDeclaration).Message);
    }

    [Fact]
    public void ValidatorRejectsWrongNamespaceAndPrivateDeclaration()
    {
        using var repository = RecipeRepository(includeTargets: true);
        Write(
            repository.Path,
            FormalPath,
            "namespace Wrong.Namespace\n\ntheorem xi_reading_reflection : True := by trivial\n\nend Wrong.Namespace\n");
        var wrongNamespace = PaperRecipeValidator.Validate(repository.Path, "D5-P001");
        Write(
            repository.Path,
            FormalPath,
            "namespace D5.S3.Zeros.CompletedZeta\n\nprivate theorem xi_reading_reflection : True := by trivial\n\nend D5.S3.Zeros.CompletedZeta\n");
        var privateDeclaration = PaperRecipeValidator.Validate(repository.Path, "D5-P001");

        Assert.Contains("Lean declaration is missing", Assert.IsType<PaperRecipeValidationOutcome.Invalid>(wrongNamespace).Message);
        Assert.Contains("Lean declaration is missing", Assert.IsType<PaperRecipeValidationOutcome.Invalid>(privateDeclaration).Message);
    }

    [Fact]
    public void GoodRecipeValidatesAndCliEmitsAStableReceipt()
    {
        using var repository = RecipeRepository(includeTargets: true);
        var firstConsole = new BufferedConsole();
        var secondConsole = new BufferedConsole();

        var validated = PaperRecipeValidator.Validate(repository.Path, "D5-P001");
        var firstExit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path),
            firstConsole);
        var secondExit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path),
            secondConsole);

        var valid = Assert.IsType<PaperRecipeValidationOutcome.Valid>(validated);
        Assert.Equal("D5-P001", valid.Recipe.Id);
        Assert.Equal(0, firstExit);
        Assert.Equal(firstConsole.Output, secondConsole.Output);
        Assert.Equal(string.Empty, firstConsole.Error);
        Assert.Equal(string.Empty, secondConsole.Error);
        Assert.Matches(
            "^PAPERGEN_VALIDATE_OK id=D5-P001 gid=D5/P/D5-P001 "
            + "recipe_sha256=sha256:[0-9a-f]{64} decls=1 blueprint=1 evidence=0 "
            + "narrative_order=2 venue=arXiv-math.NT\\n$",
            firstConsole.Output);
    }

    private static TemporaryDirectory RecipeRepository(bool includeTargets = false)
    {
        return TemporaryDirectory.Create(repositoryPath =>
        {
            Write(repositoryPath, RecipePath, CanonicalRecipe);
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(repositoryPath, FormalPath))!);
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(repositoryPath, BlueprintPath))!);
            if (includeTargets)
            {
                Write(
                    repositoryPath,
                    FormalPath,
                    "namespace D5.S3.Zeros.CompletedZeta\n\ntheorem xi_reading_reflection : True := by trivial\n\nend D5.S3.Zeros.CompletedZeta\n");
                Write(
                    repositoryPath,
                    BlueprintPath,
                    "# Completed Zeta\n");
            }
        });
    }

    private static void Write(string root, string relativePath, string content)
    {
        var path = Path.Combine(root, relativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, content, new UTF8Encoding(false, true));
    }

    private static ImmutableArray<byte> CanonicalBytes(string value) =>
        ImmutableArray.CreateRange(new UTF8Encoding(false, true).GetBytes(value));

    private static string PathFor(string gidText)
    {
        Assert.True(Gid.TryParse(gidText, out var gid));
        return gid.Path.Value;
    }

}
