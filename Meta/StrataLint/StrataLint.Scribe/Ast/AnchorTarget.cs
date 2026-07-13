using System.Collections.Immutable;

namespace StrataLint.Scribe;

public enum AnchorRegistrationStatus
{
    Resolved,
    RegisteredOpen,
}

public sealed record StructuralSelector
{
    internal StructuralSelector(
        string linePrefix,
        string? requiredToken = null,
        string? headingPrefix = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(linePrefix);
        if (headingPrefix is not null)
        {
            ArgumentException.ThrowIfNullOrWhiteSpace(headingPrefix);
        }

        LinePrefix = linePrefix;
        RequiredToken = requiredToken;
        HeadingPrefix = headingPrefix;
    }

    public string LinePrefix { get; }

    public string? RequiredToken { get; }

    public string? HeadingPrefix { get; }

    public string CanonicalString =>
        (HeadingPrefix is null ? string.Empty : "heading-prefix:" + HeadingPrefix + " && ")
        + "line-prefix:"
        + LinePrefix
        + (RequiredToken is null ? string.Empty : " && token:" + RequiredToken);
}

public abstract record AnchorTarget
{
    private protected AnchorTarget(
        string semanticKey,
        string sourceId,
        string sourcePath,
        string sourceRevision,
        string? expectedSha256,
        StructuralSelector selector)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(semanticKey);
        ArgumentException.ThrowIfNullOrWhiteSpace(sourceId);
        ArgumentException.ThrowIfNullOrWhiteSpace(sourcePath);
        ArgumentException.ThrowIfNullOrWhiteSpace(sourceRevision);
        SemanticKey = semanticKey;
        SourceId = sourceId;
        SourcePath = sourcePath;
        SourceRevision = sourceRevision;
        ExpectedSha256 = expectedSha256;
        Selector = selector ?? throw new ArgumentNullException(nameof(selector));
    }

    public abstract string TargetKind { get; }

    public string SemanticKey { get; }

    public string SourceId { get; }

    public string SourcePath { get; }

    public string SourceRevision { get; }

    public string? ExpectedSha256 { get; }

    public StructuralSelector Selector { get; }
}

public sealed record TheoryNodeTarget : AnchorTarget
{
    internal TheoryNodeTarget(
        string semanticKey,
        string sourceId,
        string sourcePath,
        string sourceRevision,
        string expectedSha256,
        StructuralSelector selector)
        : base(
            semanticKey,
            sourceId,
            sourcePath,
            sourceRevision,
            expectedSha256,
            selector)
    {
    }

    public override string TargetKind => "theory-node";
}

public sealed record SpecClauseTarget : AnchorTarget
{
    internal SpecClauseTarget(
        string semanticKey,
        string sourcePath,
        string sourceRevision,
        string expectedSha256,
        StructuralSelector selector)
        : base(
            semanticKey,
            "golden-ledger-spec-" + sourceRevision,
            sourcePath,
            sourceRevision,
            expectedSha256,
            selector)
    {
    }

    public override string TargetKind => "spec-clause";
}

public sealed record LibraryEntryTarget : AnchorTarget
{
    internal LibraryEntryTarget(
        string semanticKey,
        string sourcePath,
        string sourceRevision,
        string expectedSha256,
        StructuralSelector selector)
        : base(
            semanticKey,
            "library",
            sourcePath,
            sourceRevision,
            expectedSha256,
            selector)
    {
    }

    public override string TargetKind => "library-entry";
}

public sealed record MathlibSymbolTarget : AnchorTarget
{
    internal MathlibSymbolTarget(
        string semanticKey,
        string sourceRevision,
        StructuralSelector selector)
        : base(
            semanticKey,
            "mathlib",
            "lake-manifest.json",
            sourceRevision,
            expectedSha256: null,
            selector)
    {
    }

    public override string TargetKind => "mathlib-symbol";
}

public sealed class AnchorDefinition
{
    internal AnchorDefinition(
        Anchor anchor,
        AnchorTarget target,
        AnchorRegistrationStatus status,
        string? caseId = null,
        string? openReason = null)
    {
        Anchor = anchor ?? throw new ArgumentNullException(nameof(anchor));
        Target = target ?? throw new ArgumentNullException(nameof(target));
        Status = status;
        CaseId = caseId;
        OpenReason = openReason;
        if (status is AnchorRegistrationStatus.RegisteredOpen
            && (string.IsNullOrWhiteSpace(caseId) || string.IsNullOrWhiteSpace(openReason))
            || status is AnchorRegistrationStatus.Resolved
                && (caseId is not null || openReason is not null))
        {
            throw new ArgumentException("Anchor registration status lacks a canonical disposition.");
        }
    }

    public Anchor Anchor { get; }

    public AnchorTarget Target { get; }

    public AnchorRegistrationStatus Status { get; }

    public string? CaseId { get; }

    public string? OpenReason { get; }
}

public sealed record AnchorResolutionReceipt(
    string SourceId,
    string SourcePath,
    string SourceRevision,
    string SourceSha256,
    string StructuralSelector);

public abstract record AnchorResolution
{
    private AnchorResolution() { }

    public sealed record Resolved : AnchorResolution
    {
        internal Resolved(AnchorTarget target, AnchorResolutionReceipt receipt)
        {
            Target = target;
            Receipt = receipt;
        }

        public AnchorTarget Target { get; }

        public AnchorResolutionReceipt Receipt { get; }
    }

    public sealed record RegisteredOpen : AnchorResolution
    {
        internal RegisteredOpen(
            AnchorTarget target,
            string caseId,
            string reason,
            AnchorResolutionReceipt receipt)
        {
            Target = target;
            CaseId = caseId;
            Reason = reason;
            Receipt = receipt;
        }

        public AnchorTarget Target { get; }

        public string CaseId { get; }

        public string Reason { get; }

        public AnchorResolutionReceipt Receipt { get; }
    }

    public sealed record Unregistered : AnchorResolution
    {
        internal Unregistered(Anchor anchor) => Anchor = anchor;

        public Anchor Anchor { get; }
    }

    public sealed record InvalidTarget : AnchorResolution
    {
        internal InvalidTarget(Anchor anchor, string reason)
        {
            Anchor = anchor;
            Reason = reason;
        }

        public Anchor Anchor { get; }

        public string Reason { get; }
    }

    public sealed record Ambiguous : AnchorResolution
    {
        internal Ambiguous(Anchor anchor, string reason)
        {
            Anchor = anchor;
            Reason = reason;
        }

        public Anchor Anchor { get; }

        public string Reason { get; }
    }
}
