using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.EngineeringScope;

internal static partial class LeanCacheEnsureCommand
{
    // These two libraries moved from trureturing to leanInspector. Their former
    // namespace directories are producer-owned outputs, not dependency staleness.
    // In particular, a matching Mathlib stamp does not make them current owners.
    internal static bool RetireRootJudgeOutputs(
        string root, LeanCacheWriterGuard writerGuard, Action<string>? remove = null)
    {
        var lake = Path.Combine(root, ".lake");
        writerGuard.RequireOwnershipOf(lake);
        var config = Path.Combine(root, "lakefile.toml");
        if (!File.Exists(config)) return false;
        var package = TomlSerializer.Deserialize<TomlTable>(File.ReadAllText(config))
            ?? throw new InvalidOperationException("missing root Lake package");
        if (!package.TryGetValue("name", out var name) || !Equals(name, "trureturing")) return false;

        // Preserve a workspace that still declares the former root libraries.
        // Native adapter fixtures also retain their own root-owned driver.
        var libraries = package.TryGetValue("lean_lib", out var value)
            ? FileMapTomlTables.Parse(value, config, allowEmpty: true) : [];
        var obsolete = new List<string>();
        foreach (var library in new[] { "LeanInformationAudit", "LeanInformationAuditAnalysis" })
        {
            if (libraries.Any(table => table.TryGetValue("name", out var owner) && Equals(owner, library)))
                continue;
            foreach (var facet in new[] { "lib/lean", "ir" })
            {
                var path = Path.Combine(lake, "build", facet, library);
                if (PrivateOutputDirectory(lake, path)) obsolete.Add(path);
            }
        }
        if (obsolete.Count == 0) return false;

        // Reg may have persisted evidence while findOLean still selected the
        // former root owner. Retire its build products first, before removing
        // ANY old owner. If interrupted, an old directory remains to trigger
        // retry; after they are all gone, every Reg product has been removed.
        // No marker, report invalidation or dependency-stamp change is needed.
        var reg = Path.Combine(lake, "build", "reg");
        var hasReg = PrivateOutputDirectory(lake, reg);
        foreach (var path in obsolete) ValidateOutputTree(path);
        if (hasReg) ValidateOutputTree(reg);
        remove ??= static path => Directory.Delete(path, recursive: true);
        if (hasReg) remove(reg);
        foreach (var path in obsolete) remove(path);
        return true;
    }

    private static bool PrivateOutputDirectory(string lake, string path)
    {
        var relative = Path.GetRelativePath(lake, path);
        if (Path.IsPathRooted(relative) || relative == ".."
            || relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            throw new InvalidOperationException("cache output is outside the owned .lake directory");
        var current = lake;
        foreach (var component in new[] { string.Empty }.Concat(relative.Split(Path.DirectorySeparatorChar)))
        {
            if (component.Length != 0) current = Path.Combine(current, component);
            var attributes = OutputAttributes(current);
            if (attributes is null) return false;
            if (attributes.Value.HasFlag(FileAttributes.ReparsePoint)
                || !attributes.Value.HasFlag(FileAttributes.Directory))
                throw new InvalidOperationException($"cache output is not a private directory: {current}");
        }
        return true;
    }

    private static void ValidateOutputTree(string path)
    {
        foreach (var entry in Directory.EnumerateFileSystemEntries(path))
        {
            var attributes = File.GetAttributes(entry);
            if (attributes.HasFlag(FileAttributes.ReparsePoint))
                throw new InvalidOperationException($"cache output contains a forbidden symlink: {entry}");
            if (attributes.HasFlag(FileAttributes.Directory)) ValidateOutputTree(entry);
        }
    }

    private static FileAttributes? OutputAttributes(string path)
    {
        try { return File.GetAttributes(path); }
        catch (Exception error) when (error is FileNotFoundException or DirectoryNotFoundException)
        { return null; }
    }
}
