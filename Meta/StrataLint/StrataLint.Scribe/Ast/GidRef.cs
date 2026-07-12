using StrataLint.Engine;

namespace StrataLint.Scribe;

public interface IGidExistenceValidator
{
    bool Exists(GidRef reference);
}

public sealed class SnapshotGidExistenceValidator : IGidExistenceValidator
{
    private readonly RepositorySnapshot snapshot;

    public SnapshotGidExistenceValidator(RepositorySnapshot snapshot) =>
        this.snapshot = snapshot ?? throw new ArgumentNullException(nameof(snapshot));

    public bool Exists(GidRef reference)
    {
        ArgumentNullException.ThrowIfNull(reference);
        return snapshot.TryGetFile(reference.Path.Value, out _);
    }
}

public sealed class GidRef : IEquatable<GidRef>
{
    private GidRef(Gid gid) => Parsed = gid;

    private Gid Parsed { get; }

    public string Value => Parsed.Value;

    public RepoPath Path => Parsed.Path;

    internal bool IsFormalModule =>
        !HasExplicitPlane && Value.AsSpan(Value.LastIndexOf('/') + 1).IndexOf('.') < 0;

    internal bool IsFormalDeclaration =>
        !HasExplicitPlane && Value.AsSpan(Value.LastIndexOf('/') + 1).IndexOf('.') >= 0;

    internal bool IsBlueprint => Value.StartsWith("D5/B/", StringComparison.Ordinal);

    internal bool IsEvidence => Value.StartsWith("D5/E/", StringComparison.Ordinal);

    private bool HasExplicitPlane =>
        Value.StartsWith("D5/B/", StringComparison.Ordinal)
        || Value.StartsWith("D5/E/", StringComparison.Ordinal)
        || Value.StartsWith("D5/C/", StringComparison.Ordinal)
        || Value.StartsWith("D5/L/", StringComparison.Ordinal)
        || Value.StartsWith("D5/P/", StringComparison.Ordinal);

    public static GidRef Create(
        string value,
        IGidExistenceValidator? existenceValidator = null)
    {
        if (!Gid.TryParse(value, out var gid))
        {
            throw new ArgumentException("Value is not a canonical GID.", nameof(value));
        }

        var reference = new GidRef(gid);
        if (existenceValidator is not null && !existenceValidator.Exists(reference))
        {
            throw new ArgumentException("GID does not exist in the supplied snapshot.", nameof(value));
        }

        return reference;
    }

    public bool Equals(GidRef? other) =>
        other is not null && string.Equals(Value, other.Value, StringComparison.Ordinal);

    public override bool Equals(object? obj) => obj is GidRef other && Equals(other);

    public override int GetHashCode() => StringComparer.Ordinal.GetHashCode(Value);

    public override string ToString() => Value;
}

public sealed class LeanDeclarationRef : IEquatable<LeanDeclarationRef>
{
    private LeanDeclarationRef(
        GidRef reference,
        LeanDeclarationKind? expectedKind,
        bool requireNoSorry)
    {
        Reference = reference;
        ExpectedKind = expectedKind;
        RequireNoSorry = requireNoSorry;
    }

    public GidRef Reference { get; }

    public string Value => Reference.Value;

    public LeanDeclarationKind? ExpectedKind { get; }

    public bool RequireNoSorry { get; }

    public string DeclarationName => Value[(Value.LastIndexOf('.') + 1)..];

    public static LeanDeclarationRef Create(
        string value,
        IGidExistenceValidator? existenceValidator = null,
        LeanDeclarationKind? expectedKind = null,
        bool requireNoSorry = false)
    {
        var reference = GidRef.Create(value, existenceValidator);
        if (!reference.IsFormalDeclaration)
        {
            throw new ArgumentException("Value must select a Lean declaration.", nameof(value));
        }

        return new LeanDeclarationRef(reference, expectedKind, requireNoSorry);
    }

    public bool Equals(LeanDeclarationRef? other) =>
        other is not null
        && Reference.Equals(other.Reference)
        && ExpectedKind == other.ExpectedKind
        && RequireNoSorry == other.RequireNoSorry;

    public override bool Equals(object? obj) =>
        obj is LeanDeclarationRef other && Equals(other);

    public override int GetHashCode() =>
        HashCode.Combine(Reference, ExpectedKind, RequireNoSorry);

    public override string ToString() => Value;
}

public enum LeanDeclarationKind
{
    Axiom,
    Definition,
    Theorem,
    Opaque,
    Quotient,
    Constructor,
    Recursor,
    Inductive,
}
