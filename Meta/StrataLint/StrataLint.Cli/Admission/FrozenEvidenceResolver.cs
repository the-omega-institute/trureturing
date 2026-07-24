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

        foreach (var input in references.Inputs)
        {
            InvalidOperationException? lastFailure = null;
            var resolved = false;
            var single = FrozenLedgerReferenceSet.Create(
                ImmutableArray.Create(input),
                ImmutableArray<string>.Empty);
            foreach (var repository in repositories)
            {
                try
                {
                    _ = repository.ValidateFrozenReferences(single);
                    resolved = true;
                    break;
                }
                catch (InvalidOperationException exception)
                {
                    lastFailure = exception;
                }
            }

            if (!resolved)
            {
                throw new InvalidOperationException(
                    lastFailure?.Message ?? "frozen Git input is unavailable from every evidence repository");
            }
        }

        return TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
    }
}
