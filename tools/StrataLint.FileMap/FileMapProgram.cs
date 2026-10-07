namespace StrataLint.FileMap;

internal sealed record FileMapCommandResult(int ExitCode, string Output, string Error);

public static class FileMapProgram
{
    public static int Main(string[] args) =>
        Run(args, Environment.CurrentDirectory, Console.Out, Console.Error);

    internal static int Run(IReadOnlyList<string> arguments, string repositoryRoot,
        TextWriter output, TextWriter error)
    {
        var result = FileMapConformCommand.Run(arguments, repositoryRoot);
        output.Write(result.Output);
        error.Write(result.Error);
        return result.ExitCode;
    }
}
