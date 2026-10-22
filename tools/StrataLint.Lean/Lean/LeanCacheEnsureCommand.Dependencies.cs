using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class LeanCacheEnsureCommand
{
    private static CommandResult LinkedAdditiveFailure(
        string root, LeanPinSet pins, LeanWorktreeLocation location, string? stampMiss,
        ClonefileReceipt? clonefile, string reason) =>
        FailureReceipt("failed", root, location.MainCheckout, "clonefile-additive", pins.Sha256,
            reason + "; additive restoration did not complete; existing target artifacts were retained; "
                + "repair the reported provisioning boundary before retrying",
            stampMiss, clonefile, LeanArchiveAttempt.Skipped(LinkedArchiveDisabled));

    private static CommandResult RestoreLinkedDependencies(
        string root, LeanPinSet pins, IWorktreeProcessRunner runner, IDirectoryCloner cloner,
        LeanCacheWriterGuard writerGuard, ILeanCacheStateProbe stateProbe, Action<string>? removePartial)
    {
        var location = GitWorktreeInventory.Locate(root, runner);
        if (!location.IsLinked)
            return FailureReceipt("refused", root, null, "none", pins.Sha256,
                "--restore-dependencies requires an already-stamped linked worktree");
        var stamp = LeanCacheStamp.Inspect(Path.Combine(root, ".lake"), pins);
        if (stamp.State != LeanCacheStampState.Match)
            return FailureReceipt("refused", root, location.MainCheckout, "none", pins.Sha256,
                "--restore-dependencies requires a matching target stamp; existing cache was retained: " + stamp.Reason);
        using var selection = GitWorktreeInventory.SelectMainDonor(location, pins, runner, stateProbe);
        if (selection.Donor is null)
            return LinkedFailure(root, pins, location, selection.Notice, null);
        try
        {
            var restored = LeanDependencyLayerRestorer.Restore(selection, root, pins, runner,
                writerGuard, cloner, removePartial);
            return SuccessReceipt("restored", root, location.MainCheckout, "clonefile-additive",
                pins.Sha256, restored.Notice, LeanCacheProvisioner.InspectMathlibOleans(Path.Combine(root, ".lake")),
                clonefile: restored.Clonefile, archive: LeanArchiveAttempt.Skipped(LinkedArchiveDisabled));
        }
        catch (Exception exception)
        {
            return FailureReceipt("failed", root, location.MainCheckout, "clonefile-additive",
                pins.Sha256, exception.Message,
                clonefile: (exception as LeanCacheProvisionException)?.Clonefile,
                archive: LeanArchiveAttempt.Skipped(LinkedArchiveDisabled));
        }
    }
}
