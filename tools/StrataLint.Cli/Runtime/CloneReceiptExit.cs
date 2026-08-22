namespace StrataLint.Cli;

internal class LeanCacheProvisionException : InvalidOperationException
{
    internal LeanCacheProvisionException(
        string message,
        Exception? innerException = null,
        ClonefileReceipt? clonefile = null)
        : base(message, innerException)
    {
        Clonefile = clonefile ?? ClonefileReceipt.NotRun;
    }

    internal ClonefileReceipt Clonefile { get; }
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
        return new LeanCacheProvisionException(message, exception, Receipt);
    }

    private static string Join(string? first, string? second)
    {
        if (string.IsNullOrWhiteSpace(first)) return second ?? string.Empty;
        if (string.IsNullOrWhiteSpace(second)) return first;
        return first + "; " + second;
    }
}
