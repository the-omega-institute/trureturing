namespace StrataLint.Cli;

internal class LeanCacheProvisionException : InvalidOperationException
{
    internal LeanCacheProvisionException(
        string message,
        MathlibCachePruneOutcome pruneOutcome,
        Exception? innerException = null,
        ClonefileReceipt? clonefile = null)
        : base(message, innerException)
    {
        PruneOutcome = pruneOutcome;
        Clonefile = clonefile ?? ClonefileReceipt.NotRun;
    }

    internal MathlibCachePruneOutcome PruneOutcome { get; }

    internal ClonefileReceipt Clonefile { get; }
}

internal sealed class MathlibOleanCompletenessException : LeanCacheProvisionException
{
    internal MathlibOleanCompletenessException(
        int? missingOleanFiles,
        IReadOnlyList<string> missingOleanSamples,
        string message,
        MathlibCachePruneOutcome? pruneOutcome = null,
        Exception? innerException = null,
        ClonefileReceipt? clonefile = null)
        : base(message, pruneOutcome ?? MathlibCachePruneOutcome.NotRun, innerException, clonefile)
    {
        MissingOleanFiles = missingOleanFiles;
        MissingOleanSamples = missingOleanSamples;
    }

    internal int? MissingOleanFiles { get; }

    internal IReadOnlyList<string> MissingOleanSamples { get; }
}

/// <summary>
/// Preserves the monotonic receipt once a clonefile boundary has been crossed.
/// Every later cleanup or exceptional exit must pass through this object.
/// </summary>
internal sealed class CloneReceiptExit
{
    internal CloneReceiptExit(ClonefileReceipt receipt, string? warning = null)
    {
        Receipt = receipt;
        Warning = warning;
    }

    internal ClonefileReceipt Receipt { get; private set; }

    internal string? Warning { get; private set; }

    internal void AppendWarning(string warning) => Warning = Join(Warning, warning);

    internal bool TryCleanup(string path, Action<string> cleanup, string operation)
    {
        try
        {
            cleanup(path);
            return true;
        }
        catch (Exception exception)
        {
            Receipt = Receipt with
            {
                CleanupError = Join(Receipt.CleanupError, exception.Message),
            };
            AppendWarning($"{operation} failed ({exception.Message})");
            return false;
        }
    }

    internal LeanCacheProvisionException Wrap(Exception exception)
    {
        var message = Join(exception.Message, Warning);
        return exception switch
        {
            MathlibOleanCompletenessException completeness =>
                new MathlibOleanCompletenessException(
                    completeness.MissingOleanFiles,
                    completeness.MissingOleanSamples,
                    message,
                    completeness.PruneOutcome,
                    completeness,
                    Receipt),
            LeanCacheProvisionException provision =>
                new LeanCacheProvisionException(
                    message,
                    provision.PruneOutcome,
                    provision,
                    Receipt),
            _ => new LeanCacheProvisionException(
                message,
                MathlibCachePruneOutcome.NotRun,
                exception,
                Receipt),
        };
    }

    private static string Join(string? first, string? second)
    {
        if (string.IsNullOrWhiteSpace(first)) return second ?? string.Empty;
        if (string.IsNullOrWhiteSpace(second)) return first;
        return first + "; " + second;
    }
}
