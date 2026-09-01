namespace StrataLint.Engine;

internal enum TestMapUnknownReason
{
    VariablePath,
    DirectoryEnumeration,
    IndirectViaProductionLoader,
    MetadataUnavailable,
    RepositoryRootMarker,
    Other,
}

internal sealed record TestMapSource(
    string Path,
    string Content,
    string PartitionKey = "synthetic");

internal readonly record struct ScribeCompileTimeInputUniverse(string Prefix, string Suffix);

internal sealed record ScribeTestMethod(
    string PartitionKey,
    string SourcePath,
    string Id,
    IReadOnlyList<TestMapUnknownReason> UnknownReasons)
{
    internal bool IsUnknown => UnknownReasons.Count != 0;

    internal string Identity => $"{SourcePath}::{Id}";

    internal string DisplayIdentity => $"{PartitionKey}::{Id}";
}

internal sealed record ScribeTestMap(
    IReadOnlyList<ScribeTestMethod> Methods,
    IReadOnlyList<string> UnclassifiedManagedProjectPaths,
    IReadOnlyList<string> OrphanManagedSourcePaths,
    IReadOnlyList<string> DanglingCompileFailProofProjectExemptionPaths,
    IReadOnlyList<MsBuildCompileFinding> CompileQueryFindings);

internal sealed record ScribeTestProjectPartition(string Key, string ProjectPath);

internal sealed record ScribeTrackedSource(string Path, string Content);
