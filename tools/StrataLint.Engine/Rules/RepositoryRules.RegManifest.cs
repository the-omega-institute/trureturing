using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    [FindingEdge(FindingEdgeKind.Interaction)]
    internal static ImmutableArray<RuleFinding> DeclarationManifestAgreement(CurrentRuleContext context)
    {
        context.Current.TryGetFile("lake-manifest.json", out var root);
        context.Current.TryGetFile(RegManifestAgreement.ManifestPath, out var reg);
        var hasLakefile = context.Current.TryGetFile(RegManifestAgreement.LakefilePath, out _);
        var error = RegManifestAgreement.Validate(root?.Text, reg?.Text, hasLakefile);
        return error is null ? [] : [new RuleFinding(RegManifestAgreement.ManifestPath, error)];
    }
}
