namespace StrataLint.Tests;

[AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
public sealed class BaseFactScopeProbeAttribute : Attribute
{
    public BaseFactScopeProbeAttribute(int ruleNumber)
    {
        RuleNumber = ruleNumber;
    }

    public BaseFactScopeProbeAttribute(int ruleNumber, Type edgeOwnerType, string edgeMemberName)
    {
        RuleNumber = ruleNumber;
        EdgeOwnerType = edgeOwnerType ?? throw new ArgumentNullException(nameof(edgeOwnerType));
        EdgeMemberName = string.IsNullOrWhiteSpace(edgeMemberName)
            ? throw new ArgumentException("Edge member name is required.", nameof(edgeMemberName))
            : edgeMemberName;
    }

    public int RuleNumber { get; }

    public Type? EdgeOwnerType { get; }

    public string? EdgeMemberName { get; }
}
