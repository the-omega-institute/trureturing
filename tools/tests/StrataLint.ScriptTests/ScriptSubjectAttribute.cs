namespace StrataLint.ScriptTests;

[AttributeUsage(AttributeTargets.Class, AllowMultiple = true, Inherited = false)]
internal sealed class ScriptSubjectAttribute(string subject) : Attribute
{
    internal string Subject { get; } = subject;
}
