using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class FrozenEvidenceResolver
{
    internal static TrustedFrozenGitReferences Validate(
        FrozenLedgerReferenceSet references,
        params IRepositoryGateway[] repositories)
    {
        ArgumentNullException.ThrowIfNull(references);
        ArgumentNullException.ThrowIfNull(repositories);
        if (repositories.Length == 0 || repositories.Any(static repository => repository is null))
        {
            throw new ArgumentException("at least one frozen evidence repository is required", nameof(repositories));
        }

        if (repositories.Length == 1)
        {
            return repositories[0].ValidateFrozenReferences(references);
        }

        foreach (var oid in references.CommitOids)
        {
            Resolve(
                FrozenLedgerReferenceSet.Create(
                    ImmutableArray<FrozenLedgerInput>.Empty,
                    ImmutableArray<string>.Empty,
                    [oid],
                    Array.Empty<string>(),
                    Array.Empty<string>()),
                repositories);
        }

        foreach (var oid in references.TreeOids)
        {
            Resolve(
                FrozenLedgerReferenceSet.Create(
                    ImmutableArray<FrozenLedgerInput>.Empty,
                    ImmutableArray<string>.Empty,
                    Array.Empty<string>(),
                    [oid],
                    Array.Empty<string>()),
                repositories);
        }

        foreach (var oid in references.BlobOids)
        {
            Resolve(
                FrozenLedgerReferenceSet.Create(
                    ImmutableArray<FrozenLedgerInput>.Empty,
                    ImmutableArray<string>.Empty,
                    Array.Empty<string>(),
                    Array.Empty<string>(),
                    [oid]),
                repositories);
        }

        foreach (var input in references.Inputs)
        {
            var single = FrozenLedgerReferenceSet.Create(
                ImmutableArray.Create(input),
                ImmutableArray<string>.Empty);
            Resolve(single, repositories);
        }

        return TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
    }

    private static void Resolve(
        FrozenLedgerReferenceSet references,
        IEnumerable<IRepositoryGateway> repositories)
    {
        InvalidOperationException? lastFailure = null;
        foreach (var repository in repositories)
        {
            try
            {
                _ = repository.ValidateFrozenReferences(references);
                return;
            }
            catch (InvalidOperationException exception)
            {
                lastFailure = exception;
            }
        }

        throw new InvalidOperationException(
            lastFailure?.Message ?? "frozen Git object is unavailable from every evidence repository");
    }
}
