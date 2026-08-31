using System.Text.Json;

namespace StrataLint.EngineeringScope.SelfLockProbe;

internal static class Program
{
    internal static int Run(string[] arguments)
    {
        if (arguments.FirstOrDefault() == "evaluator-digest")
        {
            try
            {
                var controllerRoot = SingleOption(arguments.Skip(1).ToArray(), "--controller-root");
                Console.Out.WriteLine(StrictArtifacts.EvaluatorDigest(controllerRoot));
                return 0;
            }
            catch (Exception exception)
            {
                Console.Error.WriteLine("SELF_LOCK_PROBE_DIGEST_FAILED " + exception.GetType().Name);
                return 2;
            }
        }

        if (arguments.FirstOrDefault() != "evaluate")
        {
            Console.Error.WriteLine("SELF_LOCK_PROBE_BAD_ARGUMENT");
            return 2;
        }

        (ProbeResultContract Result, int ExitCode) result;
        try
        {
            result = ProbeReducer.Evaluate(ProbeOptions.Parse(arguments.Skip(1).ToArray()));
        }
        catch (Exception exception)
        {
            result = (new ProbeResultContract(
                1,
                "PROBE_INDETERMINATE",
                new AuthorizationContract(false, false, true, [], string.Empty, string.Empty),
                ["probe_input_invalid:" + exception.GetType().Name],
                []), 2);
        }
        Console.Out.WriteLine(JsonSerializer.Serialize(result.Result, ContractJson.Options));
        return result.ExitCode;
    }

    private static string SingleOption(IReadOnlyList<string> arguments, string name)
    {
        if (arguments.Count != 2 || arguments[0] != name || string.IsNullOrWhiteSpace(arguments[1]))
        {
            throw new ArgumentException("invalid evaluator-digest arguments");
        }
        return Path.GetFullPath(arguments[1]);
    }
}

internal sealed record ProbeOptions(
    string ControllerRoot,
    string PureRevertScript,
    string CandidateRepository,
    string J1Repository,
    string J1Bundle,
    string J0Repository,
    string J0Bundle,
    IReadOnlySet<GateKind> RequiredGates,
    IReadOnlySet<GateKind> RedGates)
{
    private static readonly string[] ScalarNames =
    [
        "--controller-root",
        "--pure-revert-script",
        "--candidate-repository",
        "--j1-repository",
        "--j1-bundle",
        "--j0-repository",
        "--j0-bundle",
    ];

    internal static ProbeOptions Parse(IReadOnlyList<string> arguments)
    {
        var scalars = new Dictionary<string, string>(StringComparer.Ordinal);
        var required = new HashSet<GateKind>();
        var red = new HashSet<GateKind>();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count || string.IsNullOrWhiteSpace(arguments[index + 1]))
            {
                throw new ArgumentException("options must be non-empty name/value pairs");
            }
            var name = arguments[index];
            var value = arguments[index + 1];
            if (name == "--required-gate")
            {
                if (!required.Add(ParseGate(value)))
                    throw new ArgumentException("required gate is duplicated");
            }
            else if (name == "--red-gate")
            {
                if (!red.Add(ParseGate(value)))
                    throw new ArgumentException("red gate is duplicated");
            }
            else if (ScalarNames.Contains(name, StringComparer.Ordinal))
            {
                if (!scalars.TryAdd(name, value))
                    throw new ArgumentException($"option is duplicated: {name}");
            }
            else
            {
                throw new ArgumentException($"unknown option: {name}");
            }
        }
        if (ScalarNames.Any(name => !scalars.ContainsKey(name)) || required.Count == 0)
        {
            throw new ArgumentException("required options are absent");
        }
        if (!red.IsSubsetOf(required))
        {
            throw new ArgumentException("red gates must be required gates");
        }
        return new ProbeOptions(
            Path.GetFullPath(scalars["--controller-root"]),
            Path.GetFullPath(scalars["--pure-revert-script"]),
            Path.GetFullPath(scalars["--candidate-repository"]),
            Path.GetFullPath(scalars["--j1-repository"]),
            Path.GetFullPath(scalars["--j1-bundle"]),
            Path.GetFullPath(scalars["--j0-repository"]),
            Path.GetFullPath(scalars["--j0-bundle"]),
            required,
            red);
    }

    private static GateKind ParseGate(string value) => value switch
    {
        "engineering" => GateKind.Engineering,
        "lean" => GateKind.Lean,
        "admission" => GateKind.Admission,
        _ => throw new ArgumentException($"unknown gate: {value}"),
    };
}
