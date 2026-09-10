// Loaded only by the optional build producer seed hook. The SDK Csc task
// formats its own arguments; this task never invokes the compiler.
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Xml.Linq;
using Microsoft.Build.Evaluation;
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
            inputs.Add(typeof(object).Assembly.Location);
            // File-bearing Csc parameters include modules/resources/embedded files
            // as well as sources/references/analyzers. No compiler switch list.
            foreach (var property in typeof(Microsoft.CodeAnalysis.BuildTasks.Csc).GetProperties())
            {
                if (!property.CanRead || property.GetIndexParameters().Length != 0) continue;
                var value = property.GetValue(this);
                var items = value as ITaskItem[];
                if (items != null)
                    foreach (var item in items) if (File.Exists(item.ItemSpec)) inputs.Add(Path.GetFullPath(item.ItemSpec));
                var single = value as ITaskItem;
                if (single != null && File.Exists(single.ItemSpec)) inputs.Add(Path.GetFullPath(single.ItemSpec));
                var text = value as string;
                if (!string.IsNullOrEmpty(text) && File.Exists(text)) inputs.Add(Path.GetFullPath(text));
            }
            // Re-evaluate with the actual global properties to obtain import
            // provenance, including property-only imports absent from
            // MSBuildAllProjects. Values are used here, never dumped in a seed.
            using (var collection = new ProjectCollection())
            {
                var project = new Project(JudgeProject,
                    ((IBuildEngine6)BuildEngine).GetGlobalProperties().ToDictionary(pair => pair.Key, pair => pair.Value), null, collection);
                if (!string.IsNullOrEmpty(project.GetPropertyValue("TargetFrameworks")))
                    throw new InvalidOperationException("multiple target frameworks are not seedable");
                inputs.Add(JudgeProject);
                foreach (var import in project.Imports) inputs.Add(import.ImportedProject.FullPath);
                document.Add(new XElement("configuration", string.Join("|", new[] {
                    project.GetPropertyValue("NETCoreSdkVersion"), project.GetPropertyValue("TargetFramework"),
                    project.GetPropertyValue("Configuration"), project.GetPropertyValue("Platform"),
                    project.GetPropertyValue("RuntimeIdentifier") })));
            }
            // Analyzer assemblies can load companion implementation assemblies.
            foreach (var analyzer in Analyzers ?? new ITaskItem[0])
                foreach (var companion in Directory.GetFiles(Path.GetDirectoryName(Path.GetFullPath(analyzer.ItemSpec)), "*.dll"))
                    inputs.Add(companion);
            inputs.ExceptWith(outputs);
            document.Add(new XElement("inputs", inputs.OrderBy(path => path).Select(path => new XElement("file", path))));
        }
        catch (Exception error)
        {
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
}

// Normal MSBuild Copy remains the writer. Removing a differing destination
// makes PreserveNewest repair changed bytes even when their time was preserved.
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
            File.Delete(destination);
        }
        return true;
    }
}
