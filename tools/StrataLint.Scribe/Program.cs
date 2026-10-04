namespace StrataLint.Scribe;

internal static class ScribeProgram
{
    public static int Main(string[] args) => ScribeCli.Run(
        args, Directory.GetCurrentDirectory(), Console.Out, Console.Error);
}
