namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    // Present byte changes and first pins share the protected-base delta source.
    // Rename/copy destinations have their own candidate path and are included.
    internal static IEnumerable<RepoPath> ChangedOrFirstPinD5Modules(DeltaRuleContext context) =>
        context.Changes.Paths.Select(path =>
                FrozenStatePath.TryToModulePath(path.Value, out var module)
                    ? !context.Baseline.Files.ContainsKey(path) && context.Current.Files.ContainsKey(path)
                        ? module : default
                    : IsPresentByteChangedD5Module(context, path) ? path : default)
            .OfType<RepoPath>()
            .Where(path => path.Value is { } value && value.StartsWith("D5/", StringComparison.Ordinal)
                && value.EndsWith(".lean", StringComparison.Ordinal) && context.Current.Files.ContainsKey(path))
            .Distinct().OrderBy(path => path.Value, StringComparer.Ordinal);

    internal static bool IsPresentByteChangedD5Module(DeltaRuleContext context, RepoPath path) =>
        path.Value.StartsWith("D5/", StringComparison.Ordinal)
        && path.Value.EndsWith(".lean", StringComparison.Ordinal)
        && context.Current.Files.TryGetValue(path, out var current)
        && (!context.Baseline.Files.TryGetValue(path, out var baseline)
            || !current.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan()));

    private static bool ManagedLean(RepositoryFile artifact, RuleApplicabilityContext context) =>
        LeanClosureValidator.IsManagedLean(artifact.Path.Value);

    private static bool ReportLean(RepositoryFile artifact, RuleApplicabilityContext context) =>
        LeanClosureValidator.IsReportLean(artifact.Path.Value);

    private static bool CapacityScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        !artifact.Path.Value.StartsWith("docs/develop/", StringComparison.Ordinal)
        && artifact.Path.Value != "lake-manifest.json"
        && artifact.Path.Value != BackfillInventoryLoader.RelativePath;

    private static bool Formal(RepositoryFile artifact, RuleApplicabilityContext context) =>
        artifact.Path.Value.StartsWith("D5/", StringComparison.Ordinal)
        && artifact.Path.Value.EndsWith(".lean", StringComparison.Ordinal);

    private static bool StatusScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        IsStatusScope(artifact.Path.Value);

    private static bool RepositoryScoped(RepositoryFile artifact, RuleApplicabilityContext context) => false;

    private static bool HeartsScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        artifact.Path.Value == HeartsPath
        || FrozenStatePath.IsUnderRoot(artifact.Path.Value);

    private static bool GeneralSource(RepositoryFile artifact, RuleApplicabilityContext context) =>
        Formal(artifact, context)
        && TryHeader(artifact.Text, out var header)
        && header.Generality == "G";

    private static bool DomainScoped(RepositoryFile artifact, RuleApplicabilityContext context)
    {
        var parts = artifact.Path.Value.Split('/');
        return parts.Length >= 4 && parts[0] == "D5" && IsStratum(parts[1])
            || parts.Length >= 5
                && parts[0] is "Blueprint" or "Evidence"
                && parts[1] == "D5"
                && IsStratum(parts[2]);
    }

    private static bool ToolchainScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        artifact.Path.Value is "global.json" or "lean-toolchain" or "lakefile.toml" or "lake-manifest.json"
        || artifact.Path.Value.StartsWith("Directory.Build.", StringComparison.Ordinal)
        || artifact.Path.Value.StartsWith("Directory.Packages.", StringComparison.Ordinal)
        || artifact.Path.Value.EndsWith(".csproj", StringComparison.Ordinal)
        || artifact.Path.Value.EndsWith("packages.lock.json", StringComparison.Ordinal);

    private static bool AllArtifacts(RepositoryFile artifact, RuleApplicabilityContext context) => true;

    private static bool BackfillScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        BackfillInventoryLoader.IsCanonicalPath(artifact.Path.Value);

    private static bool LiteratureScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        artifact.Path.Value == "Library/queries.yaml";

    private static bool AnchorReferenceScoped(
        RepositoryFile artifact,
        RuleApplicabilityContext context) =>
        Formal(artifact, context)
        || LiteratureScoped(artifact, context);

    private static bool ValuesScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        artifact.Path.Value == ValuesKernelBindingValidator.RelativePath
        || artifact.Path.Value.StartsWith("Evidence/D5/values.", StringComparison.Ordinal);

    private static bool StructuredOrChronicle(
        RepositoryFile artifact,
        RuleApplicabilityContext context) =>
        artifact.Path.Value.EndsWith(".json", StringComparison.Ordinal)
        || artifact.Path.Value.EndsWith(".yaml", StringComparison.Ordinal)
        || artifact.Path.Value.EndsWith(".yml", StringComparison.Ordinal)
        || artifact.Path.Value.StartsWith("Chronicle/", StringComparison.Ordinal);

    private static bool InstantiationScoped(
        RepositoryFile artifact,
        RuleApplicabilityContext context)
    {
        var parts = artifact.Path.Value.Split('/');
        var theory = parts.Length > 1 && parts[0] is "Blueprint" or "Evidence"
            ? parts[1]
            : parts[0];
        return theory is "Metallic" or "Moduli"
            || theory.Length > 1 && theory[0] == 'D' && theory != "D5" && theory[1..].All(char.IsDigit);
    }

    private static bool BootstrapScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        BootstrapGate.IsProtected(artifact.Path);

    private static bool ScribeDefinitionScoped(
        RepositoryFile artifact,
        RuleApplicabilityContext context) =>
        artifact.Path.Value.StartsWith("Blueprint/", StringComparison.Ordinal)
        && artifact.Path.Value.EndsWith(".scribe.cs", StringComparison.Ordinal);
}
