namespace StrataLint.EngineeringScope;

internal sealed record CommandResult(
    bool Success,
    string Output,
    string Error,
    int? ExitCode = null);

internal sealed record ExplicitCommandResult(int ExitCode, string Output, string Error);
