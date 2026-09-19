using System.Collections.Immutable;
using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

[CollectionDefinition(nameof(CanonicalFileMapCollection))]
public sealed class CanonicalFileMapCollection : ICollectionFixture<CanonicalFileMapFixture>;

public sealed class CanonicalFileMapFixture
{
    // The test host reads one fixed repository. Synthetic mutation fixtures keep
    // their own inputs; only these canonical-source assertions share the result.
    private readonly Lazy<ImmutableArray<FileMapFinding>> findings = new(() =>
        FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot()).ToImmutableArray());

    internal ImmutableArray<FileMapFinding> Findings => findings.Value;
}
