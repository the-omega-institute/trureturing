namespace StrataLint.Engine;

internal enum RepositoryReadPatternKind
{
    Exact,
    Subtree,
    All,
}

[AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor, AllowMultiple = true)]
internal sealed class RepositoryReadPatternAttribute(
    RepositoryReadPatternKind kind,
    string? path = null) : Attribute
{
    internal RepositoryReadPatternKind Kind { get; } = kind;

    internal string? Path { get; } = path;
}
