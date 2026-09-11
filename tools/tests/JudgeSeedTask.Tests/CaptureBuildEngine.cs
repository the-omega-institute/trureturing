using System.Collections;
using Microsoft.Build.Framework;

namespace JudgeSeedTask.Tests;

// Native Csc argument formatting uses this build engine contract.
// The seed task never queries global properties or reevaluates a project.
internal sealed class CaptureBuildEngine : IBuildEngine10
{
    internal Dictionary<string, string> Properties { get; } = new();
    internal List<BuildMessageEventArgs> Messages { get; } = [];
    public IReadOnlyDictionary<string, string> GetGlobalProperties() => Properties;
    public void LogMessageEvent(BuildMessageEventArgs e) => Messages.Add(e);
    public bool ContinueOnError => false;
    public int LineNumberOfTaskNode => 0;
    public int ColumnNumberOfTaskNode => 0;
    public string ProjectFileOfTaskNode => string.Empty;
    public bool IsRunningMultipleNodes => false;
    public bool AllowFailureWithoutError { get; set; }
    public EngineServices EngineServices { get; } = new CaptureEngineServices();
    public bool ShouldTreatWarningAsError(string warningCode) => false;
    public int RequestCores(int requestedCores) => requestedCores;
    public void ReleaseCores(int coresToRelease) { }
    public void LogErrorEvent(BuildErrorEventArgs e) => throw new InvalidOperationException(e.Message);
    public void LogWarningEvent(BuildWarningEventArgs e) => throw new InvalidOperationException(e.Message);
    public void LogCustomEvent(CustomBuildEventArgs e) => throw new NotSupportedException();
    public bool BuildProjectFile(string p, string[] t, IDictionary g, IDictionary o) => throw new NotSupportedException();
    public bool BuildProjectFile(string p, string[] t, IDictionary g, IDictionary o, string v) => throw new NotSupportedException();
    public bool BuildProjectFilesInParallel(string[] p, string[] t, IDictionary[] g, IDictionary[] o, string[] v,
        bool cache, bool unload) => throw new NotSupportedException();
    public BuildEngineResult BuildProjectFilesInParallel(string[] p, string[] t, IDictionary[] g,
        IList<string>[] remove, string[] v, bool outputs) => throw new NotSupportedException();
    public void Yield() => throw new NotSupportedException();
    public void Reacquire() => throw new NotSupportedException();
    public void RegisterTaskObject(object key, object obj, RegisteredTaskObjectLifetime lifetime, bool early) => throw new NotSupportedException();
    public object GetRegisteredTaskObject(object key, RegisteredTaskObjectLifetime lifetime) => throw new NotSupportedException();
    public object UnregisterTaskObject(object key, RegisteredTaskObjectLifetime lifetime) => throw new NotSupportedException();
    public void LogTelemetry(string eventName, IDictionary<string, string> properties) => throw new NotSupportedException();

    private sealed class CaptureEngineServices : EngineServices
    {
        public override bool LogsMessagesOfImportance(MessageImportance importance) => true;
        public override bool IsTaskInputLoggingEnabled => false;
    }
}
