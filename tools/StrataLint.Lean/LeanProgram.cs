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
            if (arguments.FirstOrDefault() is "ensure-cache" or "with-cache-reader" or "cache-git" or "warm-cache")
            {
                var root = Directory.GetCurrentDirectory();
                var rest = arguments.Skip(1).ToArray();
                var runner = new ProductionWorktreeProcessRunner();
                var result = arguments[0] switch
                {
                    "cache-git" => LeanCacheEnsureCommand.RunGit(root, rest, runner),
                    "warm-cache" => LeanCacheWarmCommand.Run(root, rest, runner, new ApfsDirectoryCloner()),
                    _ => LeanCacheEnsureCommand.Run(root, rest, runner,
                        runCommand: arguments[0] == "with-cache-reader"),
                };
                Console.Out.Write(result.Output);
                Console.Error.Write(result.Error);
                return result.ExitCode ?? (result.Success ? 0 : 2);
            }
            throw new ArgumentException("expected lean-utility-input, ensure-cache, with-cache-reader, cache-git or warm-cache");
        }
        catch (Exception exception)
        {
            Console.Error.WriteLine($"LEAN_PRODUCER_FAILED {exception.Message}");
            return 2;
        }
    }
}
