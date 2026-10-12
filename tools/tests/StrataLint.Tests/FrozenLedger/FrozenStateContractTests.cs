using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenStateContractTests
{
    private const string Path = "Golden/Frozen/state/D5/S0/Carrier/Probe.lean.json";
    private const string Pin = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    [Fact]
    public void StrictStateSchemaRejectsSingleFieldRecord()
    {
        Assert.Throws<FormatException>(() => FrozenStateRecordLoader.Load(File($"{{\"statement_id\":\"{Pin}\"}}\n")));
    }

    [Fact]
    public void StrictStateSchemaAcceptsOnlyStatementAndSortedDeclarations()
    {
        var text = $"{{\"statement_id\":\"{Pin}\",\"declarations\":[{{\"declaration_name_key\":\"ns(n0,5:probe)\",\"kind\":\"theorem\"}}]}}\n";
        Assert.Equal(Pin, FrozenStateRecordLoader.Load(File(text)).StatementId.Value);
    }

    [Theory]
    [InlineData("axiom")]
    [InlineData("constructor")]
    [InlineData("def")]
    [InlineData("inductive")]
    [InlineData("opaque")]
    [InlineData("quotient")]
    [InlineData("recursor")]
    [InlineData("theorem")]
    public void StrictStateSchemaAcceptsEveryProducerDeclarationKind(string kind)
    {
        var text = $"{{\"statement_id\":\"{Pin}\",\"declarations\":[{{\"declaration_name_key\":\"ns(n0,5:probe)\",\"kind\":\"{kind}\"}}]}}\n";

        var record = FrozenStateRecordLoader.Load(File(text));

        Assert.Equal(new FrozenDeclaration("ns(n0,5:probe)", kind), Assert.Single(record.Declarations));
        Assert.Equal(Encoding.UTF8.GetBytes(text), FrozenStateRecord.Encode(record.StatementId, record.Declarations).ToArray());
    }

    [Theory]
    [InlineData("quot")]
    [InlineData("definition")]
    [InlineData("unknown")]
    public void StrictStateSchemaRejectsUnsupportedDeclarationKind(string kind)
    {
        var text = $"{{\"statement_id\":\"{Pin}\",\"declarations\":[{{\"declaration_name_key\":\"ns(n0,5:probe)\",\"kind\":\"{kind}\"}}]}}\n";

        Assert.Throws<FormatException>(() => FrozenStateRecordLoader.Load(File(text)));
    }

    [Theory]
    [InlineData("[{\"declaration_name_key\":\"ns(n0,1:b)\",\"kind\":\"theorem\"},{\"declaration_name_key\":\"ns(n0,1:a)\",\"kind\":\"theorem\"}]")]
    [InlineData("[{\"declaration_name_key\":\"ns(n0,1:a)\",\"kind\":\"theorem\"},{\"declaration_name_key\":\"ns(n0,1:a)\",\"kind\":\"theorem\"}]")]
    [InlineData("[{\"declaration_name_key\":\"ns(n0,1:a)\",\"kind\":\"theorem\",\"statement_id\":\"unused\"}]")]
    [InlineData("[{\"declaration_name_key\":\"broken\",\"kind\":\"theorem\"}]")]
    public void StrictStateSchemaRejectsUnorderedDuplicateOrExtraDeclarationFields(string declarations)
    {
        Assert.Throws<FormatException>(() => FrozenStateRecordLoader.Load(File(
            $"{{\"statement_id\":\"{Pin}\",\"declarations\":{declarations}}}\n")));
    }

    [Fact]
    public void StateWriterProducesTheClosedSchema()
    {
        using var temporary = new TemporaryDirectory();
        Assert.True(FrozenStateWriter.Write(temporary.Path, RepoPath.CreateKnown("D5/S0/Carrier/Probe.lean"), StatementId.Create(Pin)));
        var wire = System.IO.File.ReadAllText(System.IO.Path.Combine(temporary.Path, Path));
        Assert.Equal($"{{\"statement_id\":\"{Pin}\",\"declarations\":[]}}\n", wire);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentStateChecksPinAndDeclarationInventoryIndependently(bool wrongPin)
    {
        var fixture = new RuleFixture();
        const string module = "D5/S0/Carrier/Probe.lean";
        fixture.Files[module] = "theorem probe : True := by trivial\n";
        fixture.Reports[module] = new LeanFileReport([], [new LeanDeclaration("probe", "theorem", "True", [])
        { NameKey = "ns(n0,5:probe)" }]);
        var pin = FrozenContentAddress.ComputeModuleStatementId(RepoPath.CreateKnown(module), fixture.Reports[module]).Value;
        fixture.Files[Path] = wrongPin
            ? "{\"statement_id\":\"" + Pin + "\",\"declarations\":[{\"declaration_name_key\":\"ns(n0,5:probe)\",\"kind\":\"theorem\"}]}\n"
            : "{\"statement_id\":\"" + pin + "\",\"declarations\":[]}\n";
        var findings = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(8), fixture.Build(RawChangeSet.Create([Path]))).Diagnostics;
        Assert.Contains(findings, diagnostic => diagnostic.Message.Contains(
            wrongPin ? "pin mismatch" : "declaration list mismatch", StringComparison.Ordinal));
    }

    [Fact]
    public void RepositoryStateRecordsRoundTripThroughTheStrictLoader()
    {
        var root = TestRepositoryLayout.FindRoot();
        var paths = Directory.EnumerateFiles(System.IO.Path.Combine(root, FrozenStatePath.Root), "*", SearchOption.AllDirectories).ToArray();
        Assert.NotEmpty(paths);
        foreach (var path in paths)
        {
            var relative = System.IO.Path.GetRelativePath(root, path).Replace('\\', '/');
            var bytes = System.IO.File.ReadAllBytes(path);
            var record = FrozenStateRecordLoader.Load(new(RepoPath.CreateKnown(relative), ImmutableArray.CreateRange(bytes), Encoding.UTF8.GetString(bytes)));
            Assert.Equal(bytes, FrozenStateRecord.Encode(record.StatementId, record.Declarations).ToArray());
        }
    }

    private static RepositoryFile File(string text) => new(RepoPath.CreateKnown(Path),
        ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text)), text);
}
