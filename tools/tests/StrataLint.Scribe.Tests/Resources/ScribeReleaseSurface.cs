using System.Reflection;
using System.Runtime.ExceptionServices;

namespace StrataLint.Scribe.Tests;

internal static class ScribeReleaseSurface
{
    internal const string ResourceName = "scribe-resources.zip";
    internal const string BundleFile = "StrataLint.Scribe.ResourceBundle.dll";

    internal static byte[] Bundle(byte[] bytes) => (byte[])Invoke("ScribeResourceBundle", "Write", bytes);
    internal static byte[] Unbundle(byte[] bytes) => (byte[])Invoke("ScribeResourceBundle", "ReadPackBytes", bytes);
    internal static ScribeResourcePack OpenBundle(byte[] bytes) => (ScribeResourcePack)Invoke("ScribeResourceBundle", "Open", bytes);

    private static Type RequireType(string name)
    {
        var type = typeof(ScribeResourcePack).Assembly.GetType("StrataLint.Scribe." + name);
        Assert.NotNull(type);
        Assert.True(type.IsPublic);
        return type;
    }

    private static object Invoke(string type, string name, object argument)
    {
        var method = RequireType(type).GetMethods(BindingFlags.Public | BindingFlags.Static)
            .SingleOrDefault(item => item.Name == name && item.GetParameters().Length == 1
                && item.GetParameters()[0].ParameterType.IsInstanceOfType(argument));
        Assert.NotNull(method);
        try { return method.Invoke(null, [argument])!; }
        catch (TargetInvocationException exception) when (exception.InnerException is not null)
        {
            ExceptionDispatchInfo.Capture(exception.InnerException).Throw();
            throw;
        }
    }
}
