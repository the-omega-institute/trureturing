using StrataLint.Scribe;

namespace StrataLint.Scribe.Documents;

public static class Program
{
    public static int Main(string[] args) => ScribeCli.Run(
        args is ["resources", "verify-source", "--tree-from", _]
            ? typeof(Program).Assembly
            : DocumentAssembly.Value,
        args,
        Directory.GetCurrentDirectory(),
        Console.Out,
        Console.Error);
}
