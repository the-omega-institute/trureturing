using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class Program
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static int Main(string[] arguments)
    {
        try
        {
            var options = Options.Parse(arguments);
            var changedPaths = ReadNulPaths(options.ChangesFile);
            var closure = EngineeringInputDeriver.DeriveRepository(options.RepositoryRoot);
            var decision = EngineeringScopePolicy.Evaluate(changedPaths, closure);

            foreach (var path in decision.MatchedPaths)
            {
                Console.WriteLine(
                    $"ENGINEERING_SCOPE_MATCHED {JsonSerializer.Serialize(path)} -> consumer-derived");
            }

            Console.WriteLine(
                $"ENGINEERING_SCOPE_DERIVED run={decision.Run.ToString().ToLowerInvariant()} "
                + $"matched={decision.MatchedPaths.Length} reason={Reason(decision.Reason)}");
            Console.WriteLine($"ENGINEERING_SCOPE_DERIVED_DETAIL {decision.Detail}");
            WriteResult(options.ResultFile, decision);
            return 0;
        }
        catch (Exception exception)
        {
            Console.Error.WriteLine($"ENGINEERING_SCOPE_DERIVATION_FAILED {exception.Message}");
            return 2;
        }
    }

    private static IReadOnlyList<string> ReadNulPaths(string path)
    {
        var bytes = File.ReadAllBytes(path);
        if (bytes.Length == 0)
        {
            return [];
        }

        if (bytes[^1] != 0)
        {
            throw new InvalidDataException("changed-path input must be NUL terminated");
        }

        var paths = new List<string>();
        var start = 0;
        for (var index = 0; index < bytes.Length; index++)
        {
            if (bytes[index] != 0)
            {
                continue;
            }

            if (index == start)
            {
                throw new InvalidDataException("changed-path input contains an empty path");
            }

            paths.Add(StrictUtf8.GetString(bytes.AsSpan(start, index - start)));
            start = index + 1;
        }

        return paths;
    }

    private static void WriteResult(string path, EngineeringScopeDecision decision)
    {
        var content = $"run={decision.Run.ToString().ToLowerInvariant()}\n"
            + $"matched_count={decision.MatchedPaths.Length}\n"
            + $"reason={Reason(decision.Reason)}\n";
        var temporary = path + ".tmp";
        File.WriteAllText(temporary, content, StrictUtf8);
        File.Move(temporary, path, overwrite: true);
    }

    private static string Reason(EngineeringScopeReason reason) => reason switch
    {
        EngineeringScopeReason.ConsumerDerivedInput => "consumer-derived-input",
        EngineeringScopeReason.ProvenDisjoint => "proven-disjoint",
        EngineeringScopeReason.IncompleteDerivation => "incomplete-derivation",
        _ => throw new ArgumentOutOfRangeException(nameof(reason)),
    };

    private sealed record Options(string RepositoryRoot, string ChangesFile, string ResultFile)
    {
        internal static Options Parse(IReadOnlyList<string> arguments)
        {
            string? repositoryRoot = null;
            string? changesFile = null;
            string? resultFile = null;
            for (var index = 0; index < arguments.Count; index += 2)
            {
                if (index + 1 >= arguments.Count)
                {
                    throw new ArgumentException($"option {arguments[index]} has no value");
                }

                switch (arguments[index])
                {
                    case "--repository":
                        repositoryRoot = arguments[index + 1];
                        break;
                    case "--changes-file":
                        changesFile = arguments[index + 1];
                        break;
                    case "--result-file":
                        resultFile = arguments[index + 1];
                        break;
                    default:
                        throw new ArgumentException($"unknown option: {arguments[index]}");
                }
            }

            return new Options(
                Require(repositoryRoot, "--repository"),
                Require(changesFile, "--changes-file"),
                Require(resultFile, "--result-file"));
        }

        private static string Require(string? value, string option) =>
            string.IsNullOrWhiteSpace(value)
                ? throw new ArgumentException($"{option} is required")
                : value;
    }
}
