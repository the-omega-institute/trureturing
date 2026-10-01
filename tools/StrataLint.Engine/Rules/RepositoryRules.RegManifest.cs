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
        context.Current.TryGetFile(RegManifestAgreement.HostManifestPath, out var host);
        var hostError = RegManifestAgreement.ValidateHost(root?.Text, host?.Text,
            context.Current.TryGetFile(RegManifestAgreement.HostLakefilePath, out _));
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        if (error is not null) findings.Add(new(RegManifestAgreement.ManifestPath, error));
        if (hostError is not null) findings.Add(new(RegManifestAgreement.HostManifestPath, hostError));
        return findings.ToImmutable();
    }
}
