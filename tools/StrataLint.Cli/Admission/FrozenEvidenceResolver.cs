using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

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

internal sealed class GitInfrastructureException : InvalidOperationException
{
    internal GitInfrastructureException(GitCommandFailure failure, Exception? innerException = null)
        : base("Git infrastructure failure: " + failure.Render(), innerException) =>
        Failure = failure;

    internal GitCommandFailure Failure { get; }
}
