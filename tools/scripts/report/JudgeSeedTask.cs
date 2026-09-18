// Loaded only by the optional build producer seed hook. The SDK Csc task
// formats its own arguments; this task never invokes the compiler.
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Xml.Linq;
using Microsoft.Build.Framework;
using Microsoft.Build.Utilities;

namespace StrataLint.JudgeSeed;

// Observe real MSBuild task starts, independently of the seed reconciliation
// result. These diagnostics never participate in build or cache decisions.
public sealed class CscExecutionLogger : ILogger
{
    private readonly TextWriter output;
    private readonly object sync = new object();
    private readonly Dictionary<string, int> projects = new Dictionary<string, int>(StringComparer.Ordinal);
    private readonly Dictionary<string, CompilerReasons> reasons = new Dictionary<string, CompilerReasons>();
    private IEventSource events;
    private bool finished;
    private bool unavailable;
    private int count;
    public LoggerVerbosity Verbosity { get; set; } = LoggerVerbosity.Normal;
    public string Parameters { get; set; }

    public CscExecutionLogger() : this(Console.Out) { }
    public CscExecutionLogger(TextWriter output) { this.output = output; }

    public void Initialize(IEventSource eventSource) => Observe(() =>
    {
        events = eventSource;
        events.TargetStarted += TargetStarted;
        events.TargetFinished += TargetFinished;
        events.MessageRaised += MessageRaised;
        events.TaskStarted += TaskStarted;
        events.BuildFinished += BuildFinished;
    });

    private void TaskStarted(object sender, TaskStartedEventArgs task)
    {
        if (task.TaskName != "Csc") return;
        Observe(() =>
        {
            if (string.IsNullOrEmpty(task.ProjectFile)) throw new InvalidDataException("Csc project unavailable");
            projects.TryGetValue(task.ProjectFile, out var previous);
            projects[task.ProjectFile] = previous + 1;
            count++;
            var context = Context(task.BuildEventContext);
            CompilerReasons captured = null;
            if (context != null && reasons.TryGetValue(context, out captured)) reasons.Remove(context);
            Write(new { status = "task-started", project = task.ProjectFile,
                reasons_status = captured != null && captured.Messages.Count > 0 ? "captured" : "unavailable",
                reasons = captured == null ? Array.Empty<string>() : captured.Messages.ToArray(),
                reasons_truncated = captured != null && captured.Truncated });
        });
    }

    private static string Context(BuildEventContext context) => context == null ? null
        : context.NodeId + "/" + context.ProjectContextId + "/" + context.TargetId;

    private void TargetStarted(object sender, TargetStartedEventArgs target) => Observe(() =>
    {
        var context = Context(target.BuildEventContext);
        if (target.TargetName == "_JudgeSdkCoreCompile" && context != null)
            reasons[context] = new CompilerReasons();
    });

    private void TargetFinished(object sender, TargetFinishedEventArgs target) => Observe(() =>
    {
        var context = Context(target.BuildEventContext);
        if (context != null) reasons.Remove(context);
    });

    private void MessageRaised(object sender, BuildMessageEventArgs message)
    {
        if (message.Importance != MessageImportance.Low) return;
        Observe(() =>
        {
            // Keep native text only for the registered compiler target; do not
            // format unrelated messages or infer compiler inputs from diagnostics.
            if (reasons.Count == 0) return;
            var context = Context(message.BuildEventContext);
            if (context == null || !reasons.TryGetValue(context, out var captured)) return;
            if (captured.Messages.Count == 8) { captured.Truncated = true; return; }
            var text = message.Message;
            if (text == null) return;
            if (Encoding.UTF8.GetByteCount(text) > 2048)
            {
                var bytes = 0;
                var characters = 0;
                foreach (var rune in text.EnumerateRunes())
                {
                    if (bytes + rune.Utf8SequenceLength > 2048) break;
                    bytes += rune.Utf8SequenceLength;
                    characters += rune.Utf16SequenceLength;
                }
                text = text.Substring(0, characters);
                captured.Truncated = true;
            }
            captured.Messages.Add(text);
        });
    }

    private sealed class CompilerReasons
    {
        internal readonly List<string> Messages = new List<string>();
        internal bool Truncated;
    }

    private void BuildFinished(object sender, BuildFinishedEventArgs build) => Observe(() =>
    {
        finished = true;
        Write(new { status = unavailable ? "unavailable" : "complete", count = unavailable ? (int?)null : count,
            build_succeeded = build.Succeeded,
            projects = unavailable ? null : projects.OrderBy(item => item.Key, StringComparer.Ordinal)
                .Select(item => new { project = item.Key, count = item.Value }).ToArray() });
    });

    public void Shutdown() => Observe(() =>
    {
        if (events != null)
        {
            events.TargetStarted -= TargetStarted;
            events.TargetFinished -= TargetFinished;
            events.MessageRaised -= MessageRaised;
            events.TaskStarted -= TaskStarted;
            events.BuildFinished -= BuildFinished;
        }
        reasons.Clear();
        if (!finished) WriteUnavailable();
    });

    private void Observe(Action action)
    {
        lock (sync)
        {
            try { action(); }
            catch (Exception)
            {
                unavailable = true;
                // A broken diagnostic destination must not throw into MSBuild.
                try { WriteUnavailable(); } catch (Exception) { }
            }
        }
    }

    private void WriteUnavailable() => Write(new { status = "unavailable", count = (int?)null });
    private void Write(object value) => output.WriteLine("JUDGE_CSC " + JsonSerializer.Serialize(value));
}

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
