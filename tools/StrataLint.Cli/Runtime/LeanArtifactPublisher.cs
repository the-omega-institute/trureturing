using System.Text.Json;
using System.Runtime.InteropServices;

namespace StrataLint.Cli;

internal static class LeanArtifactPublisher
{
    internal static (int Artifacts, int Mappings) Publish(string stage, string shared, string publicationParent, string root,
        IWorktreeProcessRunner runner, IDirectoryCloner cloner)
    {
        var detached = Path.Combine(publicationParent, ".stratalint-lake-publish-" + Path.GetRandomFileName());
        try
        {
            // Lake may hardlink stage artifacts to mutable build outputs. Detach the whole tree once.
            CopyDetached(stage, detached, root, runner, cloner);
            var artifacts = Files(detached, "artifacts");
            var mappings = Files(detached, "outputs");
            if (artifacts.Length == 0 || mappings.Length == 0)
                throw new InvalidOperationException("Lake warming produced no native artifacts or mappings");
            foreach (var file in mappings)
            {
                using var json = JsonDocument.Parse(File.ReadAllBytes(file));
                var map = json.RootElement;
                if (!map.TryGetProperty("service", out var service) || service.ValueKind != JsonValueKind.Null
                    || !map.TryGetProperty("data", out _) || map.TryGetProperty("repo", out _)
                    || map.TryGetProperty("scope", out _))
                    throw new InvalidOperationException("Only service-free native Lake mappings may be published: " + file);
            }
            foreach (var file in artifacts) PublishFile(file, detached, shared, overwrite: false);
            foreach (var file in mappings) PublishFile(file, detached, shared, overwrite: true);
            return (artifacts.Length, mappings.Length);
        }
        finally
        {
            if (Directory.Exists(detached)) Directory.Delete(detached, recursive: true);
        }
    }

    internal static void CopyDetached(string source, string target, string root,
        IWorktreeProcessRunner runner, IDirectoryCloner cloner)
    {
        var clone = cloner.Clone(source, target);
        if (clone.Succeeded) return;
        if (Directory.Exists(target)) Directory.Delete(target, recursive: true);
        LeanCacheProvisioner.RequireSuccess(runner.Run("cp", ["-R", source, target], root,
            LeanCacheProvisioner.DirectoryCopyBudget), "independent cache copy");
    }

    private static string[] Files(string root, string name)
    {
        var path = Path.Combine(root, name);
        if (!Directory.Exists(path)) return [];
        if (new DirectoryInfo(path).LinkTarget is not null)
            throw new InvalidOperationException("Native cache directories must not be symlinks");
        var files = new List<string>();
        void Visit(string directory)
        {
            foreach (var item in new DirectoryInfo(directory).EnumerateFileSystemInfos())
            {
                if (item.LinkTarget is not null) throw new InvalidOperationException("Native cache entries must not be symlinks");
                if (item is DirectoryInfo) Visit(item.FullName);
                else files.Add(item.FullName);
            }
        }
        Visit(path);
        return files.ToArray();
    }

    private static void PublishFile(string source, string stage, string shared, bool overwrite)
    {
        var target = Path.Combine(shared, Path.GetRelativePath(stage, source));
        if (!overwrite && File.Exists(target)) return;
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        // Do not let a runtime turn EXDEV into a non-atomic copy to the live pathname.
        if (Rename(source, target) != 0)
            throw new IOException("Atomic cache publication failed: " + Marshal.GetPInvokeErrorMessage(Marshal.GetLastPInvokeError()));
    }

    [DllImport("libc", EntryPoint = "rename", SetLastError = true)]
    private static extern int Rename(string source, string target);
}
