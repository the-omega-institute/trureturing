global using Xunit;
global using FactAttribute = Xunit.SkippableFactAttribute;
global using TheoryAttribute = Xunit.SkippableTheoryAttribute;

namespace StrataLint.ScriptTests;

[AttributeUsage(AttributeTargets.Class, AllowMultiple = false, Inherited = false)]
public sealed class ScriptSubjectAttribute(string subject) : Attribute
{
    public string Subject { get; } = subject;
}
