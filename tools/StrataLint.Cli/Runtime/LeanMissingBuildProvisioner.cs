using StrataLint.Engine;

namespace StrataLint.Cli;

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
        Action<string, LeanPinSet>? writeStamp = null)
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
        using var guard = selection.TakeGuard()
            ?? LeanCacheGuard.TryAcquireShared(Path.Combine(selection.Donor, ".lake"));
        if (guard is null)
        {
            return new LeanBuildProvisionAttempt(
                null,
                "donor cache guard is busy",
                ClonefileReceipt.NotRun);
        }

        var clone = LeanCacheProvisioner.CloneWithRetry(
            source,
            staged,
            cloner,
            LeanCacheProvisioner.RemovePartial,
            wait,
            out var cloneReceipt);
        var method = "clonefile";
        string? warning = null;
        if (!clone.Succeeded)
        {
            var exit = new CloneReceiptExit(cloneReceipt, $"clonefile failed ({clone.Message})");
            if (!exit.TryCleanup(staged, LeanCacheProvisioner.RemovePartial, "staging cleanup"))
            {
                return new LeanBuildProvisionAttempt(null, exit.Warning, exit.Receipt);
            }

            ProcessOutput copy;
            try
            {
                copy = runner.Run(
                    "cp",
                    ["-R", source, staged],
                    worktreeRoot,
                    LeanCacheProvisioner.DirectoryCopyBudget);
            }
            catch (Exception exception)
            {
                exit.AppendWarning($"ordinary copy failed ({exception.Message})");
                exit.TryCleanup(staged, LeanCacheProvisioner.RemovePartial, "staging cleanup");
                return new LeanBuildProvisionAttempt(null, exit.Warning, exit.Receipt);
            }

            if (copy.ExitCode != 0)
            {
                exit.AppendWarning(
                    $"ordinary copy failed ({LeanCacheProvisioner.Error(copy, "cp -R failed")})");
                exit.TryCleanup(staged, LeanCacheProvisioner.RemovePartial, "staging cleanup");
                return new LeanBuildProvisionAttempt(null, exit.Warning, exit.Receipt);
            }
            method = "copy";
            warning = LeanCacheProvisioner.Join(exit.Warning, "used slow ordinary copy");
            cloneReceipt = exit.Receipt;
        }

        try
        {
            LeanCacheProvisioner.VerifyPrivateDirectory(staged);
            var donorLake = Path.Combine(selection.Donor, ".lake");
            var donorIsPrivate = TryVerifyPrivateDirectory(donorLake, out var donorDirectoryReason);
            string? pinReason = null;
            var verifiedPins = donorIsPrivate
                ? LeanPinSet.TryReadWorktree(selection.Donor, out pinReason)
                : null;
            string? stampReason = null;
            var donorProject = donorIsPrivate
                ? stateProbe.ProbeOleans(Path.Combine(donorLake, "build", "lib", "lean"))
                : new OleanWarmthInspection(OleanWarmth.ProbeFailed, donorDirectoryReason);
            if (!donorIsPrivate
                || verifiedPins is null
                || !pins.HasSameBytes(verifiedPins)
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
                            ?? pinReason
                            ?? stampReason
                            ?? donorProject.Error
                            ?? "donor changed or became busy after staging; discarded staging build"),
                    cloneReceipt);
            }

            LeanCacheProvisioner.VerifyPrivateDirectory(lake);
            var beforeRename = stateProbe.InspectContentRoot(target);
            if (!beforeRename.Clear)
            {
                LeanCacheProvisioner.RemovePartial(staged);
                return new LeanBuildProvisionAttempt(
                    null,
                    LeanCacheProvisioner.Join(
                        warning,
                        beforeRename.Error
                            ?? "target .lake/build changed before publication; discarded staging build"),
                    cloneReceipt);
            }
            if (PathEntryExists(LeanCacheStamp.PathFor(lake)))
            {
                throw new InvalidOperationException(
                    "target cache stamp changed during staging; refusing to replace it");
            }

            // Known and accepted check-then-act window: .NET 10.0.11 on Unix LStats the
            // destination before rename(2), so a compatible entry created between those calls
            // can be replaced. This path holds the target .lake writer guard throughout, so a
            // competitor must bypass the lock protocol; this repository has zero such incidents
            // (CLAUDE.md section 20''). Closing it needs a platform-specific no-replace operation
            // such as renameatx_np(RENAME_EXCL), whose cost is disproportionate to that history.
            Directory.Move(staged, target);
            writeStamp(lake, pins);
            return new LeanBuildProvisionAttempt(
                new LeanCacheProvisionResult(
                    "cloned",
                    method,
                    warning,
                    LeanCacheProvisioner.InspectMathlibOleans(lake),
                    cloneReceipt),
                warning,
                cloneReceipt);
        }
        catch (Exception exception)
        {
            // Cleanup is confined to this call's own sibling staging directory. A build
            // already renamed into place is never removed here: this provisioner must not be
            // able to delete the target build root, and a published-but-unstamped build is
            // self-healing rather than broken. The next ensure sees a non-clear content root,
            // so it cannot re-enter this donor path, and falls through to ReproduceExisting,
            // which runs the producer with CacheTreeOwnership.PreExisting and publishes the
            // stamp in place without removing any pre-existing tree.
            var exit = new CloneReceiptExit(cloneReceipt, warning);
            exit.TryCleanup(staged, LeanCacheProvisioner.RemovePartial, "staging cleanup");
            throw exit.Wrap(exception);
        }
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
