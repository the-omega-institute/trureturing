namespace StrataLint.Scribe;

[AttributeUsage(AttributeTargets.Class, AllowMultiple = true, Inherited = false)]
public sealed class ScribeSharedSourceAttribute : Attribute
{
    public ScribeSharedSourceAttribute(string path) => Path = path;

    public string Path { get; }
}
