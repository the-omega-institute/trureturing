using System.Text.Json;

namespace StrataLint.ArchitectureTests;

internal static class TestMapProgram
{
    // This query does not reduce CI critical-path time: candidate-engineering already has
    // about 240 seconds of slack. It saves local feedback time (the three serial suites take
    // about 392 seconds) and makes source-to-test relationships machine-queryable. Results
    // are computed on demand and written only to stdout; no aggregate mapping is persisted.
    private static int Main(string[] arguments)
    {
        if (arguments.Length < 2 || arguments[0] != "test-map")
        {
            Console.Error.WriteLine("usage: dotnet run --project StrataLint.ArchitectureTests -- test-map <changed-path>...");
            return 2;
        }

        var repositoryRoot = Directory.GetCurrentDirectory();
        var map = ScribeTestMapDeriver.DeriveRepository(repositoryRoot);
        var selected = map.Select(arguments.Skip(1));
        var payload = new
        {
            changed_paths = arguments.Skip(1),
            tests = selected.Select(static method => new
            {
                id = method.Id,
                paths = method.Paths,
                unknown_reasons = method.UnknownReasons.Select(static reason => reason.ToString()),
            }),
            coverage = new
            {
                total_methods = map.Methods.Count,
                decidable = map.Methods.Count(static method => !method.IsUnknown),
                unknown = map.Methods.Count(static method => method.IsUnknown),
                unknown_reasons = Enum.GetValues<TestMapUnknownReason>().ToDictionary(
                    static reason => reason.ToString(),
                    reason => map.Methods.Count(method => method.UnknownReasons.Contains(reason))),
            },
        };
        Console.WriteLine(JsonSerializer.Serialize(payload, new JsonSerializerOptions { WriteIndented = true }));
        return 0;
    }
}
