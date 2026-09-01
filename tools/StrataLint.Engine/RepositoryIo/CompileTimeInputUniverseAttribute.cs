namespace StrataLint.Engine;

[AttributeUsage(
    AttributeTargets.Method | AttributeTargets.Property,
    AllowMultiple = true,
    Inherited = false)]
internal sealed class CompileTimeInputUniverseAttribute(
    string prefix,
    string suffix) : Attribute
{
    public string Prefix { get; } = prefix;

    public string Suffix { get; } = suffix;
}
