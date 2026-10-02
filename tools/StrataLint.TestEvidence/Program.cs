namespace StrataLint.TestEvidence;

public static class Program
{
    public static int Main(string[] args) => Run(args, Environment.CurrentDirectory, Console.Out, Console.Error);

    public static int Run(IReadOnlyList<string> arguments, string repositoryRoot, TextWriter output, TextWriter error)
    {
        if (arguments.FirstOrDefault() == "compile-proof")
        {
            var result = CompileProofCommand.Run(arguments.Skip(1).ToArray(), repositoryRoot);
            output.Write(result.Output);
            error.Write(result.Error);
            return result.ExitCode;
        }
        return TestEvidenceCommands.Run(arguments, output, error);
    }
}
