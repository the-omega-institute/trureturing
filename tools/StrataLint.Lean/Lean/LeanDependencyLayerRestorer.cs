using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal sealed record LeanDependencyRestoreResult(ClonefileReceipt Clonefile, int Added, int Retained)
{
    internal string Notice => $"additive dependency restore moved {Added} missing entries; "
        + $"retained {Retained} existing entries; existing bytes remain authoritative; "
        + "native Lake must validate traces and artifacts; no kernel or report validation performed";
}

/// <summary>Opt-in additive recovery, never a replacement or a warm-build inventory.</summary>
internal static class LeanDependencyLayerRestorer
{
    internal static LeanDependencyRestoreResult Restore(
        LeanCacheDonorSelection selection,
        string root,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        Action<string>? removePartial = null,
        Action<TimeSpan>? wait = null)
    {
        var lake = Path.Combine(root, ".lake");
        writerGuard.RequireOwnershipOf(lake);
        var donor = selection.Donor
            ?? throw new InvalidOperationException("dependency restore requires an available donor");
        var donorLake = Path.Combine(donor, ".lake");
        using var guard = selection.TakeGuard() ?? LeanCacheGuard.TryAcquireShared(donorLake);
        if (guard is null) throw new InvalidOperationException("donor cache guard is busy");
        RequireCompatible(donor, root, pins, runner);
        var source = Path.Combine(donorLake, "packages");
        RequireDirectory(source);
        var target = Path.Combine(lake, "packages");
        if (Attributes(target) is not null) RequireDirectory(target);
        var targetStamp = LeanCacheStamp.Inspect(lake, pins).State;
        if (targetStamp is not (LeanCacheStampState.Match or LeanCacheStampState.Missing))
            throw new InvalidOperationException("dependency target stamp is incompatible or unreadable");
        var staged = Path.Combine(lake, "packages.stage-" + Path.GetRandomFileName());
        removePartial ??= LeanCacheProvisioner.RemovePartial;
        var receipt = ClonefileReceipt.NotRun;
        try
        {
            var clone = LeanCacheProvisioner.CloneWithRetry(source, staged, cloner,
                removePartial, wait ?? LeanCacheProvisioner.WaitForRetry, out receipt);
            if (!clone.Succeeded)
                throw new InvalidOperationException($"dependency clonefile staging failed ({clone.Message})");
            RequireDirectory(staged);
            var packages = PackageNames(pins);
            // Clone once, then publish only declared packages. Never propagate unrelated exports.
            foreach (var entry in Directory.EnumerateFileSystemEntries(staged))
            {
                if (!packages.Contains(Path.GetFileName(entry))) removePartial(entry);
            }
            foreach (var package in packages)
            {
                var path = Path.Combine(staged, package);
                RequireDirectory(path);
                PrepareStaging(path, packageRoot: path);
            }
            RequireCompatible(donor, root, pins, runner);
            if (LeanCacheStamp.Inspect(lake, pins).State != targetStamp)
                throw new InvalidOperationException("dependency target stamp changed during staging");
            if (Attributes(target) is null) Directory.CreateDirectory(target);
            RequireDirectory(target);
            var added = 0;
            var retained = 0;
            foreach (var package in packages)
            {
                var packageRoot = Path.Combine(target, package);
                if (Attributes(packageRoot) is not null) RequireDirectory(packageRoot);
                AddMissing(Path.Combine(staged, package), Path.Combine(target, package),
                    ref added, ref retained, packageRoot);
            }
            removePartial(staged);
            return new LeanDependencyRestoreResult(receipt, added, retained);
        }
        catch (Exception exception)
        {
            // Only staging is owned by this call. A failed merge can leave useful additions;
            // retry is additive too, and no pre-existing output is removed on failure.
            var exit = new CloneReceiptExit(receipt);
            exit.TryCleanup(staged, removePartial, "dependency staging cleanup");
            throw exit.Wrap(exception);
        }
    }

    internal static void RequireCompatible(
        string donor, string root, LeanPinSet pins, IWorktreeProcessRunner runner)
    {
        RequireDirectory(Path.Combine(donor, ".lake"));
        RequireDirectory(Path.Combine(root, ".lake"));
        var sourcePins = LeanPinSet.TryReadWorktree(donor, out var sourceReason);
        var targetPins = LeanPinSet.TryReadWorktree(root, out var targetReason);
        // SamePartition/Sha256 cover Mathlib only. Require all declared pins and toolchain
        // bytes here; this deliberately conservative admission does not introduce a cache key.
        if (sourcePins is null || targetPins is null
            || !pins.HasSameBytes(sourcePins) || !pins.HasSameBytes(targetPins))
            throw new InvalidOperationException("dependency restore toolchain or resolved dependency pins differ "
                + $"or are unreadable ({sourceReason}; {targetReason})");
        if (!LeanCacheStamp.Matches(Path.Combine(donor, ".lake"), pins, out var stampReason))
            throw new InvalidOperationException(stampReason);
        if (LeanCacheBusyProbe.IsBusy(donor, runner))
            throw new InvalidOperationException("donor worktree is busy");
    }

    private static HashSet<string> PackageNames(LeanPinSet pins)
    {
        using var document = JsonDocument.Parse(pins.LakeManifest);
        if (document.RootElement.TryGetProperty("packagesDir", out var directory)
            && directory.GetString() != ".lake/packages")
            throw new InvalidOperationException("dependency restore requires canonical .lake/packages layout");
        var names = new HashSet<string>(StringComparer.Ordinal);
        foreach (var package in document.RootElement.GetProperty("packages").EnumerateArray())
        {
            var name = package.GetProperty("name").GetString();
            if (string.IsNullOrWhiteSpace(name) || name is "." or ".."
                || name.IndexOfAny(['/', '\\']) >= 0
                || package.GetProperty("type").GetString() != "git"
                || !LeanPinSet.ValidRevision(package.GetProperty("rev").GetString())
                || !names.Add(name))
                throw new InvalidOperationException("dependency restore requires unique resolved git packages");
        }
        return names;
    }

    internal static void PrepareStaging(string path, string? packageRoot = null)
    {
        RequireDirectory(path);
        foreach (var entry in Directory.EnumerateFileSystemEntries(path))
        {
            var attributes = File.GetAttributes(entry);
            if (attributes.HasFlag(FileAttributes.ReparsePoint))
            {
                RequirePackageFileLink(entry, packageRoot);
                continue;
            }
            var name = Path.GetFileName(entry);
            if (name is ".release" or "staging" or ".staging" or "reports" or "stratalint"
                || name.Contains(".stage-", StringComparison.Ordinal))
                LeanCacheProvisioner.RemovePartial(entry);
            else if (attributes.HasFlag(FileAttributes.Directory)) PrepareStaging(entry, packageRoot);
        }
    }

    internal static void AddMissing(string staged, string target, ref int added, ref int retained,
        string? packageRoot = null)
    {
        var incoming = File.GetAttributes(staged);
        var incomingLink = incoming.HasFlag(FileAttributes.ReparsePoint);
        // Package staging has already validated its links. Build recovery passes no package
        // root and keeps its original link prohibition, including file/directory conflicts.
        if (incomingLink && packageRoot is null)
            throw new InvalidOperationException($"dependency staging contains a forbidden symlink: {staged}");
        var existing = Attributes(target);
        if (existing is null)
        {
            if (!incomingLink && incoming.HasFlag(FileAttributes.Directory)) Directory.Move(staged, target);
            else File.Move(staged, target, overwrite: false);
            added++;
            return;
        }
        if (existing.Value.HasFlag(FileAttributes.ReparsePoint))
        {
            RequirePackageFileLink(target, packageRoot);
            retained++;
            return; // Retain the link itself; never merge through it.
        }
        if (!incomingLink && existing.Value.HasFlag(FileAttributes.Directory)
            && incoming.HasFlag(FileAttributes.Directory))
        {
            foreach (var entry in Directory.EnumerateFileSystemEntries(staged))
                AddMissing(entry, Path.Combine(target, Path.GetFileName(entry)), ref added, ref retained, packageRoot);
        }
        else retained++; // Includes incomplete files and file/directory conflicts; Lake owns validity.
    }

    private static void RequirePackageFileLink(string path, string? packageRoot)
    {
        var link = packageRoot is null ? null : new FileInfo(path).LinkTarget;
        void Refuse() => throw new InvalidOperationException($"dependency cache contains a forbidden symlink: {path}");
        if (string.IsNullOrEmpty(link) || Path.IsPathRooted(link)) Refuse();
        var current = Path.GetDirectoryName(path)!;
        var parts = link!.Split(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
        for (var index = 0; index < parts.Length; index++)
        {
            var part = parts[index];
            if (part is "" or ".") continue;
            if (part == "..")
            {
                if (current == packageRoot) Refuse();
                current = Path.GetDirectoryName(current)!;
                continue;
            }
            current = Path.Combine(current, part);
            var attributes = File.GetAttributes(current);
            // Inspect each original component before any '..' normalization. Link chains,
            // loops and directory links are refused without resolving or traversing them.
            if (attributes.HasFlag(FileAttributes.ReparsePoint)
                || (index < parts.Length - 1 && !attributes.HasFlag(FileAttributes.Directory))) Refuse();
        }
        var resolved = File.GetAttributes(current);
        if (resolved.HasFlag(FileAttributes.Directory) || resolved.HasFlag(FileAttributes.ReparsePoint)) Refuse();
    }

    private static void RequireDirectory(string path)
    {
        var attributes = File.GetAttributes(path);
        if (!attributes.HasFlag(FileAttributes.Directory) || attributes.HasFlag(FileAttributes.ReparsePoint))
            throw new InvalidOperationException($"dependency cache requires a private directory: {path}");
    }

    private static FileAttributes? Attributes(string path)
    {
        try { return File.GetAttributes(path); }
        catch (Exception exception) when (exception is FileNotFoundException or DirectoryNotFoundException)
        { return null; }
    }

    internal static ClonefileReceipt Combine(ClonefileReceipt first, ClonefileReceipt second) => new(
        first.Attempts + second.Attempts, [.. first.Errnos, .. second.Errnos],
        string.IsNullOrEmpty(first.CleanupError) ? second.CleanupError
            : LeanCacheProvisioner.Join(first.CleanupError, second.CleanupError));
}
