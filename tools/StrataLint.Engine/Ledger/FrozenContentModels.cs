using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using Dunet;

namespace StrataLint.Engine;

internal static class FrozenHashDomains
{
    internal const string Statement = "trureturing:statement:v1\0";
    internal const string FrozenNode = "trureturing:frozen-node:v2\0";
    internal const string FrozenGraph = "trureturing:frozen-graph:v1\0";
    internal const string FrozenEvent = "trureturing:frozen-event:v1\0";
    internal const string FrozenEventSet = "trureturing:frozen-event-set:v1\0";
    internal const string FrozenCase = "trureturing:frozen-case:v2\0";
    internal const string FrozenCaseIdentity = "trureturing:frozen-case-identity:v1\0";
    internal const string FrozenClass = "trureturing:frozen-class:v1\0";
    internal const string FrozenCorpus = "trureturing:frozen-corpus:v2\0";
    internal const string RuleCatalog = "trureturing:rule-catalog:v1\0";
}

internal static class FrozenContentHash
{
    internal static string Compute(string domain, ReadOnlySpan<byte> material)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        hash.AppendData(Encoding.UTF8.GetBytes(domain));
        hash.AppendData(material);
        return "sha256:" + Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    internal static ImmutableArray<byte> Raw(string taggedHash)
    {
        if (!FrozenHashSyntax.IsSha256(taggedHash))
        {
            throw new FormatException("Expected an algorithm-tagged SHA-256 value.");
        }

        return ImmutableArray.CreateRange(Convert.FromHexString(taggedHash[7..]));
    }
}

internal static partial class FrozenHashSyntax
{
    [GeneratedRegex("^sha256:[0-9a-f]{64}$", RegexOptions.CultureInvariant)]
    private static partial Regex Sha256Pattern();

    [GeneratedRegex("^(?:git-sha1:[0-9a-f]{40}|git-sha256:[0-9a-f]{64})$", RegexOptions.CultureInvariant)]
    private static partial Regex GitOidPattern();

    internal static bool IsSha256(string value) => Sha256Pattern().IsMatch(value);

    internal static bool IsGitOid(string value) => GitOidPattern().IsMatch(value);
}

public sealed record StatementId
{
    private StatementId(string value) => Value = value;

    public string Value { get; }

    internal static StatementId Create(string value) => new(value);

    public override string ToString() => Value;
}

public sealed record FrozenNodeId
{
    private FrozenNodeId(string value) => Value = value;

    public string Value { get; }

    internal static FrozenNodeId Create(string value) => new(value);

    public override string ToString() => Value;
}

public sealed record FrozenDeclarationStatement(
    string DeclarationNameKey,
    string Kind,
    StatementId StatementId);

public sealed record FrozenNodeMaterial(
    RepoPath RepoPath,
    ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds,
    StatementId StatementId,
    FrozenNodeId FrozenNodeId,
    ImmutableArray<FrozenNodeId> PrerequisiteFrozenNodeIds,
    ImmutableArray<string> AxiomClosure);

public sealed class FrozenMaterialCatalog
{
    private FrozenMaterialCatalog(
        ImmutableDictionary<RepoPath, TruthState> states,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency,
        ImmutableArray<FrozenNodeMaterial> closedNodes,
        ImmutableDictionary<RepoPath, FrozenNodeMaterial> byPath,
        ImmutableDictionary<RepoPath, ImmutableArray<CaseId>> openCases,
        ImmutableDictionary<RepoPath, ImmutableArray<string>> tailRegistrations)
    {
        States = states;
        Adjacency = adjacency;
        ClosedNodes = closedNodes;
        ByPath = byPath;
        OpenCases = openCases;
        TailRegistrations = tailRegistrations;
    }

    public ImmutableArray<FrozenNodeMaterial> ClosedNodes { get; }

    public ImmutableDictionary<RepoPath, ImmutableArray<CaseId>> OpenCases { get; }

    public ImmutableDictionary<RepoPath, ImmutableArray<string>> TailRegistrations { get; }

    internal ImmutableDictionary<RepoPath, FrozenNodeMaterial> ByPath { get; }

    internal ImmutableDictionary<RepoPath, TruthState> States { get; }

    internal ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> Adjacency { get; }

    internal static FrozenMaterialCatalog Create(
        ImmutableDictionary<RepoPath, TruthState> states,
        ImmutableArray<FrozenNodeMaterial> closedNodes,
        ImmutableDictionary<RepoPath, ImmutableArray<CaseId>> openCases,
        ImmutableDictionary<RepoPath, ImmutableArray<string>> tailRegistrations,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>>? adjacency = null) =>
        new(
            states,
            adjacency ?? ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>>.Empty,
            closedNodes,
            closedNodes.ToImmutableDictionary(static node => node.RepoPath),
            openCases,
            tailRegistrations);
}

[Union(EnableImplicitConversions = false)]
public partial record FrozenMaterialOutcome
{
    public partial record Accepted
    {
        internal Accepted(FrozenMaterialCatalog capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public FrozenMaterialCatalog Capability { get; }
    }

    public partial record Rejected(string Message);
}
