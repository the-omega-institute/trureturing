using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class InformationTemplateHistoryWorkspace
{
    internal static void Prepare(string candidateRoot, string work, string identity,
        ImmutableArray<RawRepositoryEntry> files, IGitProcessRunner runner)
    {
        work = Path.GetFullPath(work);
        candidateRoot = Path.GetFullPath(candidateRoot);
        if (work == candidateRoot || work.StartsWith(candidateRoot + Path.DirectorySeparatorChar, StringComparison.Ordinal)
            || candidateRoot.StartsWith(work + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            throw new IOException("history execution directory must be outside the candidate repository");
        var marker = Path.Combine(work, ".git", "information-template-history");
        if (Directory.Exists(work) && Directory.EnumerateFileSystemEntries(work).Any())
        {
            InformationTemplateHistoryBundle.RequireFile(marker);
            if (File.ReadAllText(marker) != identity + "\n")
                throw new IOException("history execution directory belongs to a different plan");
            var present = GitRepositorySnapshotReader.ReadCurrent(work);
            if (present.Entries.Length != files.Length || present.Entries.Any(e => !files.Any(f =>
                f.Path == e.Path && f.GitMode == e.GitMode && f.Bytes.AsSpan().SequenceEqual(e.Bytes.AsSpan()))))
                throw new IOException("history prepared inputs changed");
            return;
        }
        Directory.CreateDirectory(work);
        if (new DirectoryInfo(work).LinkTarget is not null) throw new IOException("history work directory is a symlink");
        var ancestors = new HashSet<string>(StringComparer.Ordinal);
        foreach (var entry in files)
        {
            InformationTemplateHistoryInputs.Plain(entry);
            FileMapSymlinkPolicy.RequirePlainAncestors(work, entry.Path, ancestors);
            var target = Path.Combine(work, entry.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.WriteAllBytes(target, entry.Bytes.AsSpan());
            if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(target,
                entry.GitMode == "100755" ? UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute
                    | UnixFileMode.GroupRead | UnixFileMode.GroupExecute | UnixFileMode.OtherRead | UnixFileMode.OtherExecute
                    : UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.GroupRead | UnixFileMode.OtherRead);
        }
        Git(["-c", "init.templateDir=", "init", "--quiet"]);
        Git(["config", "--local", "core.autocrlf", "false"]);
        Git(["config", "--local", "core.filemode", "true"]);
        Directory.CreateDirectory(Path.Combine(work, ".git", "info"));
        File.WriteAllText(Path.Combine(work, ".git", "info", "exclude"), ".lake/\n**/bin/\n**/obj/\n");
        Git(["-c", "core.hooksPath=/dev/null", "add", "--force", "--pathspec-from-file=-", "--pathspec-file-nul"],
            Encoding.UTF8.GetBytes(string.Concat(files.Select(e => e.Path + "\0"))));
        File.WriteAllText(marker, identity + "\n");

        void Git(string[] args, ReadOnlyMemory<byte> stdin = default)
        {
            var result = runner.Run("git", args, work, TimeSpan.FromMinutes(2), standardInput: stdin);
            if (result.ExitCode != 0) throw new IOException("history private index failed: " + Encoding.UTF8.GetString(result.StandardError));
        }
    }

    internal static void Publish(string source, string destination)
    {
        destination = Path.GetFullPath(destination);
        if (Path.GetFullPath(source) == destination) return;
        var parent = Path.GetDirectoryName(destination)!;
        Directory.CreateDirectory(parent);
        var staged = Path.Combine(parent, ".history-stage-" + Guid.NewGuid().ToString("N"));
        var backup = Path.Combine(parent, ".history-old-" + Guid.NewGuid().ToString("N"));
        try
        {
            Directory.CreateDirectory(staged);
            foreach (var name in InformationTemplateHistoryBundle.Suffixes.Select(s => InformationTemplateHistoryBundle.ReportName + s).Append("history.json"))
                File.Copy(Path.Combine(source, name), Path.Combine(staged, name));
            if (Directory.Exists(destination))
            {
                var allowed = InformationTemplateHistoryBundle.Suffixes.Select(s => InformationTemplateHistoryBundle.ReportName + s)
                    .Append("history.json").ToHashSet(StringComparer.Ordinal);
                if (new DirectoryInfo(destination).LinkTarget is not null
                    || Directory.EnumerateFileSystemEntries(destination).Any(p => !allowed.Contains(Path.GetFileName(p))))
                    throw new IOException("history refuses to replace a directory containing unrelated artifacts");
                Directory.Move(destination, backup);
            }
            try { Directory.Move(staged, destination); }
            catch { if (Directory.Exists(backup)) Directory.Move(backup, destination); throw; }
        }
        finally
        {
            if (Directory.Exists(staged)) Directory.Delete(staged, true);
            if (Directory.Exists(backup)) Directory.Delete(backup, true);
        }
    }
}
