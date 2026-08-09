using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal enum FrozenReferenceRejectionKind
{
    MissingObject,
    WrongObjectType,
    InvalidReference,
}

internal enum GitCommandFailureKind
{
    NonzeroExit,
    ExecutableNotFound,
    Timeout,
    Io,
    InvalidOutput,
    Process,
}

internal sealed record GitCommandFailure(
    GitCommandFailureKind Kind,
    string Executable,
    ImmutableArray<string> Arguments,
    int? ExitCode,
    int? NativeErrorCode,
    string StandardError,
    string Detail)
{
    internal string Render()
    {
        var command = Arguments.IsDefaultOrEmpty
            ? Executable
            : Executable + " " + string.Join(' ', Arguments);
        var classification = Kind switch
        {
            GitCommandFailureKind.NonzeroExit => "nonzero-exit",
            GitCommandFailureKind.ExecutableNotFound => "executable-not-found",
            GitCommandFailureKind.Timeout => "timeout",
            GitCommandFailureKind.Io => "io",
            GitCommandFailureKind.InvalidOutput => "invalid-output",
            GitCommandFailureKind.Process => "process",
            _ => throw new InvalidOperationException("unknown Git command failure kind"),
        };
        var exit = ExitCode is { } exitCode ? $", exit {exitCode}" : string.Empty;
        var native = NativeErrorCode is { } nativeCode ? $", native-error {nativeCode}" : string.Empty;
        var stderr = StandardError.Length > 0 ? $", stderr: {StandardError}" : string.Empty;
        var detail = Detail.Length > 0 ? $", detail: {Detail}" : string.Empty;
        return $"{command} [{classification}{exit}{native}{stderr}{detail}]";
    }
}

internal sealed class FrozenReferenceRejectionException : InvalidOperationException
{
    internal FrozenReferenceRejectionException(
        FrozenReferenceRejectionKind kind,
        string message,
        GitCommandFailure? gitFailure = null)
        : base(gitFailure is null ? message : $"{message}; {gitFailure.Render()}")
    {
        Kind = kind;
        GitFailure = gitFailure;
    }

    internal FrozenReferenceRejectionKind Kind { get; }

    internal GitCommandFailure? GitFailure { get; }
}

internal sealed class GitInfrastructureException : InvalidOperationException
{
    internal GitInfrastructureException(GitCommandFailure failure, Exception? innerException = null)
        : base("Git infrastructure failure: " + failure.Render(), innerException) =>
        Failure = failure;

    internal GitCommandFailure Failure { get; }
}

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
        FrozenReferenceRejectionException? lastFailure = null;
        foreach (var repository in repositories)
        {
            try
            {
                _ = repository.ValidateFrozenReferences(references);
                return;
            }
            catch (FrozenReferenceRejectionException exception)
            {
                lastFailure = exception;
            }
        }

        throw lastFailure ?? new FrozenReferenceRejectionException(
            FrozenReferenceRejectionKind.MissingObject,
            "frozen Git object is unavailable from every evidence repository");
    }
}
