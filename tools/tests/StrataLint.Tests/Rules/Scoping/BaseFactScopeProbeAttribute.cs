namespace StrataLint.Tests;

[AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
public sealed class BaseFactScopeProbeAttribute(int ruleNumber) : Attribute
{
    public int RuleNumber { get; } = ruleNumber;
}
