using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal abstract record BlueprintPinValidationOutcome
{
    private BlueprintPinValidationOutcome() { }

    internal sealed record Accepted(
        string TargetGid,
        string Generality,
        int AnchorCount,
        int ImportCount,
        ImmutableArray<string> Unverified) : BlueprintPinValidationOutcome;

    internal sealed record Rejected(ImmutableArray<string> Diagnostics) : BlueprintPinValidationOutcome;
}

internal static class BlueprintPinValidator
{
    internal static BlueprintPinValidationOutcome Validate(
        ValidatedPolicy policy,
        RepositorySnapshot repository,
        BlueprintPinManifest manifest)
    {
        ArgumentNullException.ThrowIfNull(policy);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(manifest);

        if (manifest.RouteManifest is not
            {
                Plane: "F",
                Artifact: "lean",
                Selector.Length: 0,
                Tag.Length: 0,
            })
        {
            return Rejected("pin manifest must describe one F-layer Lean file");
        }

        var route = RouteEngine.Route(policy, manifest.RouteManifest);
        if (route is RouteOutcome.Rejected routeRejected)
        {
            return Rejected($"{routeRejected.RuleId.Value} route: {routeRejected.Message}");
        }

        var routed = (RouteOutcome.Routed)route;
        var diagnostics = ImmutableArray.CreateBuilder<string>();
        ValidateAnchors(manifest.Anchors, diagnostics);
        ValidateImports(repository, manifest, diagnostics);
        if (diagnostics.Count > 0)
        {
            return new BlueprintPinValidationOutcome.Rejected(
                diagnostics.Order(StringComparer.Ordinal).ToImmutableArray());
        }

        var unverified = manifest.RouteManifest.Generality == "I"
            ? ImmutableArray.Create(
                "generality I is structurally permitted; metadata cannot decide whether the statement is freely generalizable and therefore required to be G")
            : ImmutableArray<string>.Empty;
        return new BlueprintPinValidationOutcome.Accepted(
            routed.Result.Gid.Value,
            manifest.RouteManifest.Generality,
            manifest.Anchors.Length,
            manifest.Imports.Length,
            unverified);
    }

    private static void ValidateAnchors(
        ImmutableArray<string> anchors,
        ImmutableArray<string>.Builder diagnostics)
    {
        foreach (var anchor in anchors)
        {
            if (Anchor.TryParseCanonical(anchor) is AnchorParseResult.Invalid invalid)
            {
                diagnostics.Add($"anchor '{anchor}' is not accepted: {invalid.Message}");
            }
        }

    }

    private static void ValidateImports(
        RepositorySnapshot repository,
        BlueprintPinManifest manifest,
        ImmutableArray<string>.Builder diagnostics)
    {
        foreach (var import in manifest.Imports)
        {
            if (!Gid.TryParse(import, out var gid)
                || !string.Equals(gid.Value, import, StringComparison.Ordinal)
                || !repository.TryGetFile(gid.Path.Value, out var file)
                || !RepositoryRules.TryHeader(file.Text, out var header)
                || !string.Equals(header.Gid, import, StringComparison.Ordinal))
            {
                diagnostics.Add($"import '{import}' does not resolve to a canonical formal file header");
                continue;
            }

            if (manifest.RouteManifest.Generality == "G" && header.Generality is "I" or "E")
            {
                diagnostics.Add(
                    $"G artifact imports {header.Generality} fact {gid.Path.Value}");
            }
        }
    }

    private static BlueprintPinValidationOutcome Rejected(string diagnostic) =>
        new BlueprintPinValidationOutcome.Rejected(ImmutableArray.Create(diagnostic));
}
