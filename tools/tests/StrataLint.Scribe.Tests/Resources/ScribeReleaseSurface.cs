using System.Reflection;
using System.Runtime.ExceptionServices;

namespace StrataLint.Scribe.Tests;

internal static class ScribeReleaseSurface
{
    internal const string Schema = "trureturing.scribe.release-identity";
    internal const string Commit = "0123456789abcdef0123456789abcdef01234567";
    internal const string ResourceName = "scribe-resources.zip";
    internal const string BundleFile = "StrataLint.Scribe.ResourceBundle.dll";

    internal static object Identity(int version, int count, string digest) => Activator.CreateInstance(
        RequireType("ScribeReleaseIdentity"), Schema, Commit, version, count, digest)!;

    internal static byte[] Encode(object identity) => (byte[])Invoke("ScribeReleaseIdentityCodec", "Encode", identity);
    internal static object Decode(byte[] bytes) => Invoke("ScribeReleaseIdentityCodec", "Decode", bytes);
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
