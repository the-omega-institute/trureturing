using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.TestSupport;

namespace StrataLint.TestSupport;

internal sealed class TemporaryRepository : IDisposable
{
    private readonly DirectoryInfo root = TemporaryFileSystem.Directory.CreateTempSubdirectory(
        "stratalint-statement-reconciliation-");
    private readonly List<(string Name, string Type)> pinnedDeclarations = [];

    public string Path => root.FullName;

    public static TemporaryRepository WithReport(string type)
    {
        var repository = new TemporaryRepository();
        TemporaryFileSystem.Directory.CreateDirectory(System.IO.Path.Combine(repository.Path, "Golden", "Projection"));
        TemporaryFileSystem.Directory.CreateDirectory(System.IO.Path.Combine(repository.Path, ".lake", "build", "stratalint"));
        TemporaryFileSystem.Directory.CreateDirectory(System.IO.Path.Combine(repository.Path, "Blueprint"));
        TemporaryFileSystem.File.WriteAllText(System.IO.Path.Combine(repository.Path, "global.json"), "{}\n");
        TemporaryFileSystem.File.WriteAllText(
            System.IO.Path.Combine(repository.Path, "Golden", "Projection", "statement-projection-expansion-v1.json"),
            """{"schema":"statement-projection-expansion-fixture-v1","declarations":[]}""");
        TemporaryFileSystem.File.WriteAllText(
            System.IO.Path.Combine(repository.Path, ".lake", "build", "stratalint", "raw-lean-report.json"),
            """{"modules":[{"declarations":[{"name":"D5.Test.declaration","type":"statement-v1(uparams=[],type=es(l0))"}]}]}""");
        repository.AddPinnedDeclaration("D5.Test.declaration", type);
        return repository;
    }

    public void AddPinnedDeclaration(string name, string type)
    {
        pinnedDeclarations.Add((name, type));
        var declarations = string.Join(
            ",",
            pinnedDeclarations.Select(static item =>
                $$"""{"name":{{JsonSerializer.Serialize(item.Name)}},"type":{{JsonSerializer.Serialize(item.Type)}}}"""));
        TemporaryFileSystem.File.WriteAllText(
            System.IO.Path.Combine(Path, "Golden", "Projection", "statement-projection-pilot-v1.json"),
            $$"""{"schema":"statement-projection-pilot-fixture-v1","declarations":[{{declarations}}]}""");
    }

    public LeanAxiomReport Report(string kind = "theorem") => LeanAxiomReport.Create(
        new Dictionary<string, LeanFileReport>
        {
            ["D5/Test.lean"] = new(
                [],
                [new LeanDeclaration(
                    "D5.Test.declaration",
                    kind,
                    "statement-v1(uparams=[],type=es(l0))",
                    [])]),
        });

    public DeclarationCatalog Catalog(string kind = "theorem") =>
        DeclarationCatalog.Create(Report(kind));

    public void Dispose() => root.Delete(recursive: true);
}
