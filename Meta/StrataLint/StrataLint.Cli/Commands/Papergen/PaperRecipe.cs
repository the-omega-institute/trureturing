using System.Collections.Immutable;
using System.Runtime.ExceptionServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record PaperRecipe(
    string Id,
    ImmutableArray<Gid> Declarations,
    ImmutableArray<Gid> Blueprint,
    ImmutableArray<Gid> Evidence,
    ImmutableArray<string> NarrativeOrder,
    string Venue);

internal abstract record PaperRecipeLoadOutcome
{
    internal sealed record Loaded(PaperRecipe Recipe, ImmutableArray<byte> Bytes) : PaperRecipeLoadOutcome;

    internal sealed record Invalid(string Message) : PaperRecipeLoadOutcome;
}

internal static class PaperRecipeLoader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly string[] SchemaKeys =
        ["blueprint", "decls", "evidence", "id", "narrative_order", "venue"];

    internal static PaperRecipeLoadOutcome Load(ImmutableArray<byte> bytes, string fileName)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(fileName);
        if (bytes.IsDefault)
        {
            return Invalid("recipe bytes are unavailable");
        }

        if (bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
        {
            return Invalid("recipe must not contain a UTF-8 BOM");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes.AsSpan());
        }
        catch (DecoderFallbackException)
        {
            return Invalid("recipe must be strict UTF-8");
        }

        Dictionary<string, object?> mapping;
        try
        {
            var canonical = StructuredCanonicalWriter.WriteYaml(text);
            if (!canonical.AsSpan().SequenceEqual(bytes.AsSpan()))
            {
                return Invalid("recipe does not have canonical bytes");
            }

            mapping = (Dictionary<string, object?>)YamlSubsetParser.Parse(text);
        }
        catch (FormatException exception)
        {
            return Invalid($"recipe YAML is invalid: {exception.Message}");
        }

        if (!mapping.Keys.SequenceEqual(SchemaKeys, StringComparer.Ordinal))
        {
            return Invalid("recipe schema keys must be exactly blueprint, decls, evidence, id, narrative_order, venue");
        }

        if (mapping["id"] is not string id || id.Length == 0)
        {
            return Invalid("id must be non-empty");
        }

        var expectedId = Path.GetFileNameWithoutExtension(fileName);
        if (!string.Equals(Path.GetExtension(fileName), ".yaml", StringComparison.Ordinal)
            || !string.Equals(id, expectedId, StringComparison.Ordinal))
        {
            return Invalid($"recipe id {id} does not match filename {fileName}");
        }

        if (!Gid.TryParse($"D5/P/{id}", out var paperGid)
            || paperGid.ToTarget() is not Target.Paper { Frozen: false })
        {
            return Invalid("id must be a canonical A11 paper id");
        }

        var declarations = Gids(mapping["decls"], "decls", static target =>
            target is Target.Formal { Declaration: not null }, "formal declaration GID");
        if (declarations.Error is not null) return Invalid(declarations.Error);
        // Per key, not on the shared Gids helper: evidence is legitimately empty.
        if (declarations.Values.IsEmpty) return Invalid("decls must be a non-empty sequence");

        var blueprint = Gids(mapping["blueprint"], "blueprint", static target =>
            target is Target.Blueprint, "Blueprint GID");
        if (blueprint.Error is not null) return Invalid(blueprint.Error);

        var evidence = Gids(mapping["evidence"], "evidence", static target =>
            target is Target.Evidence, "Evidence GID");
        if (evidence.Error is not null) return Invalid(evidence.Error);

        var narrative = Strings(mapping["narrative_order"], "narrative_order", requireNonEmpty: true);
        if (narrative.Error is not null) return Invalid(narrative.Error);

        if (mapping["venue"] is not string venue || string.IsNullOrWhiteSpace(venue))
        {
            return Invalid("venue must be non-empty");
        }

        return new PaperRecipeLoadOutcome.Loaded(
            new PaperRecipe(
                id,
                declarations.Values,
                blueprint.Values,
                evidence.Values,
                narrative.Values,
                venue),
            bytes);
    }

    private static (ImmutableArray<Gid> Values, string? Error) Gids(
        object? raw,
        string key,
        Func<Target, bool> accepts,
        string expected)
    {
        var strings = Strings(raw, key, requireNonEmpty: false);
        if (strings.Error is not null) return ([], strings.Error);

        var gids = ImmutableArray.CreateBuilder<Gid>();
        foreach (var value in strings.Values)
        {
            if (!Gid.TryParse(value, out var gid) || !accepts(gid.ToTarget()))
            {
                return ([], $"{key} entry must be a canonical {expected}: {value}");
            }

            gids.Add(gid);
        }

        return (gids.ToImmutable(), null);
    }

    private static (ImmutableArray<string> Values, string? Error) Strings(
        object? raw,
        string key,
        bool requireNonEmpty)
    {
        if (raw is not List<object?> list)
        {
            return ([], $"{key} must be a sequence");
        }

        if (requireNonEmpty && list.Count == 0)
        {
            return ([], $"{key} must be a non-empty sequence");
        }

        var values = ImmutableArray.CreateBuilder<string>();
        foreach (var item in list)
        {
            if (item is not string value || string.IsNullOrWhiteSpace(value))
            {
                return ([], $"{key} entries must be non-empty strings");
            }

            values.Add(value);
        }

        return (values.ToImmutable(), null);
    }

    private static PaperRecipeLoadOutcome.Invalid Invalid(string message) => new(message);
}

internal abstract record PaperRecipeValidationOutcome
{
    internal sealed record Valid(PaperRecipe Recipe, string RecipeSha256) : PaperRecipeValidationOutcome;

    internal sealed record Invalid(string Message) : PaperRecipeValidationOutcome;
}

internal static class PaperRecipeValidator
{
    /// The frozen-ledger capabilities are taken here rather than resolved from the repository
    /// root because trust cannot be reconstructed from a path: TrustedFrozenGitReferences comes
    /// from IRepositoryGateway.ValidateFrozenReferences, which resolves every recorded object
    /// through the repository itself.
    ///
    /// A recipe may only name declarations the frozen ledger actually carries. Reading the source
    /// and matching text -- what this did before -- certifies declarations that were never frozen,
    /// that belong to a revoked node, or that were added after their module was attested.
    internal static PaperRecipeValidationOutcome Validate(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        string id)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(id);
        if (!Gid.TryParse($"D5/P/{id}", out var paperGid)
            || paperGid.ToTarget() is not Target.Paper { Frozen: false })
        {
            return Invalid("paper id must be canonical A11");
        }

        var recipePath = Path.Combine(repositoryRoot, paperGid.Path.Value);
        if (!File.Exists(recipePath))
        {
            return Invalid($"recipe file is missing: {paperGid.Path.Value}");
        }

        var bytes = ImmutableArray.CreateRange(File.ReadAllBytes(recipePath));
        var loaded = PaperRecipeLoader.Load(bytes, Path.GetFileName(recipePath));
        if (loaded is PaperRecipeLoadOutcome.Invalid invalid)
        {
            return Invalid(invalid.Message);
        }

        var material = (PaperRecipeLoadOutcome.Loaded)loaded;
        foreach (var gid in material.Recipe.Declarations
            .Concat(material.Recipe.Blueprint)
            .Concat(material.Recipe.Evidence))
        {
            var targetPath = Path.Combine(repositoryRoot, gid.Path.Value);
            if (!File.Exists(targetPath))
            {
                return Invalid($"GID {gid.Value} target file is missing: {gid.Path.Value}");
            }

        }

        var resolution = ResolveActiveFrozenLedger(repositoryRoot, repository, leanReportSource);
        if (resolution is FrozenLedgerResolution.Failed failed)
        {
            return failed.Failure;
        }

        var (ledger, report) = (FrozenLedgerResolution.Ready)resolution;

        foreach (var gid in material.Recipe.Declarations)
        {
            if (!IsActivelyFrozen(gid, ledger, report))
            {
                return Invalid($"GID {gid.Value} is not an active frozen declaration");
            }
        }

        var hash = Convert.ToHexStringLower(SHA256.HashData(material.Bytes.AsSpan()));
        return new PaperRecipeValidationOutcome.Valid(material.Recipe, "sha256:" + hash);
    }


    /// Builds the authoritative active view by running the engine's own preparation. Replaying
    /// the ledger here instead would be a second implementation of its semantics, and the ledger
    /// is the single source of that truth.
    ///
    /// Failures are two different kinds and must not be merged. A ledger that is absent or does
    /// not describe this repository is a verdict about the repository, and comes back as Invalid.
    /// A raw Lean report that cannot be read or parsed is infrastructure -- the report is a build
    /// artefact, not a claim -- so it is allowed to propagate for the command to classify. The
    /// report is loaded inside preparation's callback, so its failures are tagged on the way out
    /// rather than being swept up by the ledger's catch.
    private abstract record FrozenLedgerResolution
    {
        internal sealed record Ready(FrozenLedgerConsistent Ledger, LeanAxiomReport Report)
            : FrozenLedgerResolution;

        internal sealed record Failed(PaperRecipeValidationOutcome.Invalid Failure)
            : FrozenLedgerResolution;
    }

    private static FrozenLedgerResolution
        ResolveActiveFrozenLedger(
            string repositoryRoot,
            IRepositoryGateway repository,
            ILeanReportSource leanReportSource)
    {
        // No File.Exists probe: it answers false for an unreadable path as readily as for an
        // absent one, which would report a ledger we were never allowed to look at as a content
        // fault. Preparation distinguishes the two, so the exception type decides. Its markers are
        // deliberately not caught here -- they are the environment failing, and PapergenCommand
        // turns them into the infrastructure exit.
        try
        {
            var context = DagLedgerCommandPreparation.Prepare(
                repositoryRoot,
                repository,
                leanReportSource);
            return new FrozenLedgerResolution.Ready(context.Baseline, context.Report);
        }
        catch (Exception exception) when (exception is FileNotFoundException or DirectoryNotFoundException)
        {
            return new FrozenLedgerResolution.Failed(
                Invalid($"frozen ledger is missing: {FrozenLedgerChangeClassifier.AcceptedRoot}: {exception.Message}"));
        }
        catch (Exception exception) when (exception is InvalidOperationException or FormatException)
        {
            return new FrozenLedgerResolution.Failed(
                Invalid($"frozen ledger is not usable: {FrozenLedgerChangeClassifier.AcceptedRoot}: {exception.Message}"));
        }
    }

    /// Membership is two coordinates, not one: the active node for the declaration's own module,
    /// and that node's own declaration set. Matching a leaf name across the whole ledger would
    /// certify a declaration from a different module.
    private static bool IsActivelyFrozen(Gid gid, FrozenLedgerConsistent ledger, LeanAxiomReport report)
    {
        if (gid.ToTarget() is not Target.Formal { Declaration: not null } formal)
        {
            return false;
        }

        string nameKey;
        try
        {
            nameKey = DigestionFormalizationReceipt.ResolveSignature(gid, report).NameKey;
        }
        catch (FormatException)
        {
            return false;
        }

        return ledger.ActiveFrozenNodes.Any(node =>
            node.RepoPath == formal.Path
            && node.DeclarationStatementIds.Any(statement =>
                string.Equals(statement.DeclarationNameKey, nameKey, StringComparison.Ordinal)));
    }

    private static PaperRecipeValidationOutcome.Invalid Invalid(string message) => new(message);
}
