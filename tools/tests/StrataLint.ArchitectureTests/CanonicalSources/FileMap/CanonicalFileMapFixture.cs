using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.EngineeringScope;

namespace StrataLint.ArchitectureTests;

[CollectionDefinition(nameof(CanonicalFileMapCollection))]
public sealed class CanonicalFileMapCollection : ICollectionFixture<CanonicalFileMapFixture>;

public sealed class CanonicalFileMapFixture
{
    // The test host reads one fixed repository. Synthetic mutation fixtures keep
    // their own inputs; only these canonical-source assertions share the result.
    // These assertions consume registry references, three data-verifier entries,
    // and the Blueprint Markdown pattern. Keep the complete path index and
    // global registry/actor/inventory checks without reading unrelated bodies.
    private readonly Lazy<ImmutableArray<FileMapFinding>> findings = new(() =>
        FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot(), new FileMapInspectionScope(
            ["lean-report-inputs.json", "Meta/ci-checks.json", "Meta/engineering-projects.json",
                "Blueprint/D5/S0/Carrier/Ring.md"], Actors: true, Inventory: true)).ToImmutableArray());

    internal ImmutableArray<FileMapFinding> Findings => findings.Value;
}
