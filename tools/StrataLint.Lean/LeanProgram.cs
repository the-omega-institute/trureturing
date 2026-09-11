using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class LeanProgram
{
    public static int Main(string[] arguments)
    {
        try
        {
            if (arguments.FirstOrDefault() == "lean-utility-input")
            {
                var result = LeanUtilityInputCommand.Run(
                    () => GitRepositorySnapshotReader.ReadCurrent(Directory.GetCurrentDirectory()), arguments.Skip(1).ToArray());
                Console.Out.Write(result.Output);
                Console.Error.Write(result.Error);
                return result.ExitCode;
            }
            if (arguments.FirstOrDefault() == "lean-cache-writer")
            {
                var result = LeanCacheEnsureCommand.RunWithWriter(Directory.GetCurrentDirectory(),
                    arguments.Skip(1).ToArray(), new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner());
                Console.Out.Write(result.Output);
                Console.Error.Write(result.Error);
                return result.ExitCode ?? (result.Success ? 0 : 2);
            }
            throw new ArgumentException("expected lean-utility-input or lean-cache-writer");
        }
        catch (Exception exception)
        {
            Console.Error.WriteLine($"LEAN_PRODUCER_FAILED {exception.Message}");
            return 2;
        }
    }
}
