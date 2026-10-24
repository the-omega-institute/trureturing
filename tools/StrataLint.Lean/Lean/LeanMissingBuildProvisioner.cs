using StrataLint.Runtime;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record LeanBuildProvisionAttempt(
    LeanCacheProvisionResult? Result,
    string? Warning,
    ClonefileReceipt Clonefile);

internal static class LeanMissingBuildProvisioner
{
    internal static LeanBuildProvisionAttempt TryProvision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        ILeanCacheStateProbe stateProbe,
        Action<TimeSpan>? wait = null,
        Action<string, LeanPinSet>? writeStamp = null,
        bool restoreDependencies = false)
    {
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(stateProbe);
        ArgumentNullException.ThrowIfNull(writerGuard);
        writerGuard.RequireOwnershipOf(Path.Combine(worktreeRoot, ".lake"));
        wait ??= LeanCacheProvisioner.WaitForRetry;
        writeStamp ??= LeanCacheStamp.WriteNew;
        if (selection.Donor is null)
        {
            return new LeanBuildProvisionAttempt(null, selection.Notice, ClonefileReceipt.NotRun);
        }

        var lake = Path.Combine(worktreeRoot, ".lake");
        LeanCacheProvisioner.VerifyPrivateDirectory(lake);
        var source = Path.Combine(selection.Donor, ".lake", "build");
        var target = Path.Combine(lake, "build");
        var staged = Path.Combine(lake, "build.stage-" + Path.GetRandomFileName());
        // An admitted existing build may contain a prior publication or worker progress.
        // Keep its bytes authoritative; the writer guard excludes cooperative mutation.
        var mergeExistingBuild = restoreDependencies && PathEntryExists(target);
        bool CanPublishBuild()
        {
            if (!mergeExistingBuild)
                return CanRestoreBuild(target, stateProbe, allowEmpty: restoreDependencies);
            LeanCacheProvisioner.VerifyPrivateDirectory(target);
            return true;
        }
        using var guard = selection.TakeGuard()
            ?? LeanCacheGuard.TryAcquireShared(Path.Combine(selection.Donor, ".lake"));
        if (guard is null)
        {
            return new LeanBuildProvisionAttempt(
                null,
                "donor cache guard is busy",
                ClonefileReceipt.NotRun);
        }
        if (restoreDependencies)
            LeanDependencyLayerRestorer.RequireCompatible(selection.Donor, worktreeRoot, pins, runner);

        var clone = LeanCacheProvisioner.CloneWithRetry(
            source,
            staged,
            cloner,
            LeanCacheProvisioner.RemovePartial,
            wait,
            out var cloneReceipt);
        string? warning = null;
        if (!clone.Succeeded)
        {
            var exit = new CloneReceiptExit(cloneReceipt, $"clonefile failed ({clone.Message})");
            exit.TryCleanup(staged, LeanCacheProvisioner.RemovePartial, "staging cleanup");
            throw new LeanCacheProvisionException(
                LeanCacheProvisioner.Join(exit.Warning, "donor build clonefile seeding failed"),
                clonefile: exit.Receipt);
        }

        try
        {
            LeanCacheProvisioner.VerifyPrivateDirectory(staged);
            var donorLake = Path.Combine(selection.Donor, ".lake");
            var donorIsPrivate = TryVerifyPrivateDirectory(donorLake, out var donorDirectoryReason);
            string? stampReason = null;
            var donorProject = donorIsPrivate
                ? stateProbe.ProbeOleans(Path.Combine(donorLake, "build", "lib", "lean"))
                : new OleanWarmthInspection(OleanWarmth.ProbeFailed, donorDirectoryReason);
            if (!donorIsPrivate
                || !LeanCacheStamp.Matches(
                    donorLake,
                    pins,
                    out stampReason)
                || LeanCacheBusyProbe.IsBusy(selection.Donor, runner)
                || !donorProject.IsWarm)
            {
                LeanCacheProvisioner.RemovePartial(staged);
                return new LeanBuildProvisionAttempt(
                    null,
                    LeanCacheProvisioner.Join(
                        warning,
                        donorDirectoryReason
                            ?? stampReason
                            ?? donorProject.Error
                            ?? "donor changed or became busy after staging; discarded staging build"),
                    cloneReceipt);
            }

            LeanCacheProvisioner.VerifyPrivateDirectory(lake);
            if (!CanPublishBuild())
            {
                LeanCacheProvisioner.RemovePartial(staged);
                return new LeanBuildProvisionAttempt(
                    null,
                    LeanCacheProvisioner.Join(
                        warning,
                        "target .lake/build changed before publication; discarded staging build"),
                    cloneReceipt);
            }
            if (PathEntryExists(LeanCacheStamp.PathFor(lake)))
            {
                throw new InvalidOperationException(
                    "target cache stamp changed during staging; refusing to replace it");
            }

            if (restoreDependencies)
            {
                try
                {
                    var restored = LeanDependencyLayerRestorer.Restore(selection, worktreeRoot, pins,
                        runner, writerGuard, cloner, wait: wait);
                    cloneReceipt = LeanDependencyLayerRestorer.Combine(cloneReceipt, restored.Clonefile);
                    warning = restored.Notice;
                    LeanDependencyLayerRestorer.PrepareStaging(staged);
                    if (!CanPublishBuild()
                        || PathEntryExists(LeanCacheStamp.PathFor(lake)))
                        throw new InvalidOperationException("target build or stamp changed during dependency staging");
                }
                catch (LeanCacheProvisionException exception)
                {
                    cloneReceipt = LeanDependencyLayerRestorer.Combine(cloneReceipt, exception.Clonefile);
                    throw;
                }
            }

            // Known and accepted check-then-act window: .NET 10.0.11 on Unix LStats the
            // destination before rename(2), so a compatible entry created between those calls
            // can be replaced. This path holds the target .lake writer guard throughout, so a
            // competitor must bypass the lock protocol; this repository has zero such incidents
            // (CLAUDE.md section 20''). Closing it needs a platform-specific no-replace operation
            // such as renameatx_np(RENAME_EXCL), whose cost is disproportionate to that history.
            if (restoreDependencies && Directory.Exists(target))
            {
                var added = 0;
                var retained = 0;
                LeanDependencyLayerRestorer.AddMissing(staged, target, ref added, ref retained);
                LeanCacheProvisioner.RemovePartial(staged);
            }
            else Directory.Move(staged, target);
            writeStamp(lake, pins);
            return new LeanBuildProvisionAttempt(
                new LeanCacheProvisionResult(
                    "cloned",
                    "clonefile",
                    warning,
                    LeanCacheProvisioner.InspectMathlibOleans(lake),
                    cloneReceipt),
                warning,
                cloneReceipt);
        }
        catch (Exception exception)
        {
            // Cleanup is confined to this call's own sibling staging directory. A build
            // already renamed into place is never removed here; the ensure owner selects the
            // recovery policy for a published-but-unstamped target.
            var exit = new CloneReceiptExit(cloneReceipt, warning);
            exit.TryCleanup(staged, LeanCacheProvisioner.RemovePartial, "staging cleanup");
            throw exit.Wrap(exception);
        }
    }

    internal static bool CanRestoreBuild(string path, ILeanCacheStateProbe probe, bool allowEmpty = true)
    {
        if (probe.InspectContentRoot(path).Clear) return true;
        if (!allowEmpty) return false;
        try
        {
            var attributes = File.GetAttributes(path);
            return attributes.HasFlag(FileAttributes.Directory)
                && !attributes.HasFlag(FileAttributes.ReparsePoint)
                && !Directory.EnumerateFileSystemEntries(path).Any();
        }
        catch (Exception exception) when (exception is FileNotFoundException or DirectoryNotFoundException)
        { return false; }
    }

    private static bool TryVerifyPrivateDirectory(string path, out string? reason)
    {
        try
        {
            if (!Directory.Exists(path))
            {
                reason = "donor .lake disappeared after staging";
                return false;
            }
            if (File.GetAttributes(path).HasFlag(FileAttributes.ReparsePoint))
            {
                reason = "donor .lake became a symlink after staging";
                return false;
            }
            reason = null;
            return true;
        }
        catch (Exception exception) when (exception is IOException
            or UnauthorizedAccessException
            or System.Security.SecurityException)
        {
            reason = $"donor .lake could not be revalidated after staging: {exception.Message}";
            return false;
        }
    }

    private static bool PathEntryExists(string path)
    {
        try
        {
            _ = File.GetAttributes(path);
            return true;
        }
        catch (Exception exception) when (exception is FileNotFoundException
            or DirectoryNotFoundException)
        {
            return false;
        }
    }
}
