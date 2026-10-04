namespace StrataLint.Scribe;

public static class Program
{
    public static int Main(string[] args) => ScribeCli.Run(
        args, Directory.GetCurrentDirectory(), Console.Out, Console.Error);
}
