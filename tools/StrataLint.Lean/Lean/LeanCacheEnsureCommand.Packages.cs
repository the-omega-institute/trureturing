using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class LeanCacheEnsureCommand
{
    private static CommandResult ProvisionLinkedPackagesFromMain(
        string root,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        LeanCacheWriterGuard writerGuard,
        ILeanCacheStateProbe stateProbe,
        LeanWorktreeLocation location,
        OleanWarmthInspection projectWarmth,
        string? stampMiss,
        out CacheState? cacheState,
        ClonefileReceipt? priorClonefile = null)
    {
        cacheState = null;
        var clonefile = priorClonefile ?? ClonefileReceipt.NotRun;
        try
        {
            using var selection = GitWorktreeInventory.SelectMainDonor(
                location,
                pins,
                runner,
                stateProbe);
            if (selection.Donor is null)
                return LinkedFailure(root, pins, location, selection.Notice, stampMiss, clonefile);

            var provisioned = LeanMissingPackagesProvisioner.Provision(
                selection,
                root,
                pins,
                runner,
                writerGuard,
                cloner,
                stateProbe);
            clonefile = CombineClonefileReceipts(clonefile, provisioned.Clonefile);
            return SuccessWithState(
                SuccessReceipt(
                    "seeded",
                    root,
                    location.MainCheckout,
                    provisioned.Method,
                    pins.Sha256,
                    provisioned.Warning,
                    provisioned.MathlibOleans,
                    stampMiss,
                    clonefile,
                    LeanArchiveAttempt.Skipped(LinkedArchiveDisabled)),
                root,
                projectWarmth,
                stateProbe,
                out cacheState,
                writerGuard,
                runner);
        }
        catch (Exception exception)
        {
            if (exception is LeanCacheProvisionException provisionException)
                clonefile = CombineClonefileReceipts(clonefile, provisionException.Clonefile);
            return LinkedFailure(root, pins, location, exception.Message, stampMiss, clonefile);
        }
    }

    private static ClonefileReceipt CombineClonefileReceipts(
        ClonefileReceipt first, ClonefileReceipt second) => new(
            first.Attempts + second.Attempts,
            first.Errnos.Concat(second.Errnos).ToArray(),
            JoinReasons(first.CleanupError, second.CleanupError));
}
