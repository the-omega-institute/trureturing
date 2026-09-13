// Loaded only by the optional build producer seed hook. The SDK Csc task
// formats its own arguments; this task never invokes the compiler.
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Xml.Linq;
using Microsoft.Build.Framework;
using Microsoft.Build.Utilities;

namespace StrataLint.JudgeSeed;

public sealed class JudgeSeedInputs : Microsoft.CodeAnalysis.BuildTasks.Csc
{
    [Required] public string JudgeRoot { get; set; }
    [Required] public string JudgeProject { get; set; }
    [Required] public string JudgeCapture { get; set; }
    [Required] public string JudgeIntermediate { get; set; }
    [Required] public string JudgeOutput { get; set; }
    public string JudgeCompilerOverrides { get; set; }
    public ITaskItem[] JudgeInputs { get; set; }
    public ITaskItem[] JudgeOutputs { get; set; }
    [Output] public bool JudgeCaptured { get; set; }
    [Output] public string JudgeRegistrationError { get; set; }

    public override bool Execute()
    {
        var document = new XElement("compile", new XAttribute("project", JudgeProject),
            new XAttribute("root", JudgeRoot), new XAttribute("obj", Path.GetFullPath(JudgeIntermediate)),
            new XAttribute("bin", Path.GetFullPath(JudgeOutput)));
        var outputs = new HashSet<string>((JudgeOutputs ?? new ITaskItem[0])
            .Select(item => Path.GetFullPath(item.ItemSpec)), StringComparer.Ordinal);
        document.Add(new XElement("outputs", outputs.OrderBy(path => path).Select(path => new XElement("file", path))));
        try
        {
            if (!string.IsNullOrEmpty(JudgeCompilerOverrides) || !string.IsNullOrEmpty(KeyContainer))
                throw new InvalidOperationException("custom compiler/response files/key container are not seedable");
            if (Path.GetFullPath(JudgeIntermediate) != Path.Combine(Path.GetDirectoryName(JudgeProject), "obj") + Path.DirectorySeparatorChar
                || Path.GetFullPath(JudgeOutput) != Path.Combine(Path.GetDirectoryName(JudgeProject), "bin") + Path.DirectorySeparatorChar)
                throw new InvalidOperationException("custom material directories are not seedable");
            document.Add(new XElement("arguments", GenerateCommandLineCommands() + "\n" + GenerateResponseFileCommands()),
                new XElement("environment", string.Join("\n", EnvironmentVariables ?? new string[0])),
                new XElement("runtime", Environment.Version + "|" + CultureInfo.CurrentCulture.Name + "|" + CultureInfo.CurrentUICulture.Name));
            var inputs = new HashSet<string>((JudgeInputs ?? new ITaskItem[0])
                .Select(item => Path.GetFullPath(item.ItemSpec)), StringComparer.Ordinal);
            // This is the fixed file-parameter contract of JudgeSeed.targets.
            // Check membership only; never discover additional inputs from the SDK,
            // project imports, task properties or an analyzer's neighbours.
            foreach (var items in new[] { Sources, References, Resources, AdditionalFiles,
                EmbeddedFiles, Analyzers, AnalyzerConfigFiles, LinkResources })
                foreach (var item in items ?? Array.Empty<ITaskItem>())
                    RequireRegistered(item.ItemSpec, inputs);
            foreach (var path in new[] { ApplicationConfiguration, CodeAnalysisRuleSet,
                KeyFile, Win32Icon, Win32Manifest, Win32Resource, SourceLink })
                if (!string.IsNullOrEmpty(path)) RequireRegistered(path, inputs);
            foreach (var path in AddModules ?? Array.Empty<string>()) RequireRegistered(path, inputs);
            inputs.ExceptWith(outputs);
            foreach (var path in inputs)
                if (!File.Exists(path)) throw new InvalidOperationException("required registered material is absent: " + path);
            document.Add(new XElement("inputs", inputs.OrderBy(path => path).Select(path => new XElement("file", path))));
        }
        catch (Exception error)
        {
            JudgeRegistrationError = error.Message;
            document.Add(new XElement("unsupported", error.Message));
        }
        try
        {
            Directory.CreateDirectory(Path.GetDirectoryName(JudgeCapture));
            document.Save(JudgeCapture);
            JudgeCaptured = true;
        }
        catch (IOException error) { Log.LogMessage(MessageImportance.Low, "JUDGE_SEED capture unavailable: " + error.Message); }
        catch (UnauthorizedAccessException error) { Log.LogMessage(MessageImportance.Low, "JUDGE_SEED capture unavailable: " + error.Message); }
        return true;
    }

    private static void RequireRegistered(string path, HashSet<string> inputs)
    {
        if (!inputs.Contains(Path.GetFullPath(path)))
            throw new InvalidOperationException("unregistered compiler material: " + path);
    }

}

// Repair byte differences before timestamp-based MSBuild Copy. Stage the source
// first: a source read/copy failure must leave the existing destination intact.
public sealed class JudgeSeedCopies : Task
{
    public ITaskItem[] SourceFiles { get; set; }
    public ITaskItem[] DestinationFiles { get; set; }
    public string DestinationFolder { get; set; }

    public override bool Execute()
    {
        var sources = SourceFiles ?? new ITaskItem[0];
        for (var index = 0; index < sources.Length; index++)
        {
            var source = sources[index].ItemSpec;
            var destination = DestinationFiles != null ? DestinationFiles[index].ItemSpec
                : Path.Combine(DestinationFolder, Path.GetFileName(source));
            if (Path.GetFullPath(source) == Path.GetFullPath(destination) || !File.Exists(destination)) continue;
            using (var sha = SHA256.Create())
            using (var input = File.OpenRead(source))
            using (var output = File.OpenRead(destination))
                if (sha.ComputeHash(input).SequenceEqual(sha.ComputeHash(output))
                    && (OperatingSystem.IsWindows() || File.GetUnixFileMode(source) == File.GetUnixFileMode(destination))) continue;
            var temporary = destination + ".judge-copy-" + Guid.NewGuid().ToString("N");
            try
            {
                File.Copy(source, temporary);
                File.Move(temporary, destination, overwrite: true);
            }
            finally { if (File.Exists(temporary)) File.Delete(temporary); }
        }
        return true;
    }
}
