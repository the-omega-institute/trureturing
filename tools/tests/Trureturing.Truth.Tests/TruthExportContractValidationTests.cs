using System;
using System.Collections.Immutable;
using System.Globalization;
using System.Linq;
using System.Text;
using System.Text.Json;
using Trureturing.Truth;
using Xunit;

namespace Trureturing.Truth.Tests;

public sealed class TruthExportContractValidationTests
{
    private const string Commit40 = "1111111111111111111111111111111111111111";
    private const string Tree40 = "2222222222222222222222222222222222222222";
    private const string Commit64 = "1111111111111111111111111111111111111111111111111111111111111111";
    private const string Tree64 = "2222222222222222222222222222222222222222222222222222222222222222";

    [Fact]
    public void DeclarationKindsAreExactlyTheProducerAndContractLiterals()
    {
        // tools/lean-inspector/Inspector.lean kindOf is the producer source for every literal:
        // axiomInfo -> axiom, defnInfo -> def, thmInfo -> theorem, opaqueInfo -> opaque,
        // quotInfo -> quotient, ctorInfo -> constructor, recInfo -> recursor, and
        // inductInfo -> inductive. CanonicalStatementWriter and the historical Engine-to-wire
        // TruthExportModel.Create projection copy that value unchanged; "definition" is not emitted.
        Assert.Equal(
            new[] { "axiom", "constructor", "def", "inductive", "opaque", "quotient", "recursor", "theorem" },
            TruthExportValidation.DeclarationKinds.OrderBy(static value => value, StringComparer.Ordinal));
    }

    [Fact]
    public void WriterRejectsInvalidModelPassedDirectlyWithoutCreate()
    {
        var invalid = ModelOf(Node("A.lean", 'a'),
            Node("B.lean", 'a'));

        Assert.Throws<FormatException>(() => TruthExportJsonWriter.Write(invalid));
    }

    [Fact]
    public void WriterRejectsUnsupportedRootIdentityFields()
    {
        var model = ModelOf();

        Assert.Throws<FormatException>(() => TruthExportJsonWriter.Write(model with { Schema = "wrong" }));
        Assert.Throws<FormatException>(() => TruthExportJsonWriter.Write(model with { SchemaVersion = 2 }));
        Assert.Throws<FormatException>(() => TruthExportJsonWriter.Write(model with { Dialect = "wrong" }));
        Assert.Throws<FormatException>(() => TruthExportJsonWriter.Write(model with { Producer = "Impostor" }));
    }

    [Fact]
    public void WriterRejectsNullAxiomClosureEntry()
    {
        var node = Node("A.lean", 'a') with
        {
            NodeAxiomClosure = ImmutableArray.CreateRange(new string[] { null! }),
        };

        Assert.Throws<FormatException>(() => TruthExportJsonWriter.Write(ModelOf(node)));
    }

    [Fact]
    public void WriterRejectsNullDeclarationNameKey()
    {
        var node = Node("A.lean", 'a') with
        {
            Declarations = ImmutableArray.Create(new TruthExportDeclaration(null!, "theorem", Id('1'))),
        };

        Assert.Throws<FormatException>(() => TruthExportJsonWriter.Write(ModelOf(node)));
    }

    [Fact]
    public void CreateComparesDeclarationOrderByNameKeyThenStatementId()
    {
        var node = Node("A.lean", 'a') with
        {
            Declarations = ImmutableArray.Create(
                new TruthExportDeclaration("a\0", "theorem", Id('2')),
                new TruthExportDeclaration("a", "theorem", Id('1'))),
        };

        var model = TruthExportModel.Create(ImmutableArray.Create(node), Commit40, Tree40);

        Assert.Equal(new[] { "a", "a\0" },
            model.Nodes[0].Declarations.Select(static declaration => declaration.DeclarationNameKey));
    }

    [Theory]
    [InlineData(40)]
    [InlineData(64)]
    public void ReaderAcceptsMatchingGitObjectFormats(int length)
    {
        var model = Model(
            nodes: ImmutableArray<TruthExportNode>.Empty,
            sourceCommit: new string('1', length),
            sourceTree: new string('2', length));

        var actual = Read(model);

        Assert.Equal(length, actual.SourceCommit.Length);
        Assert.Equal(length, actual.SourceTree.Length);
    }

    [Theory]
    [InlineData(39)]
    [InlineData(41)]
    [InlineData(63)]
    [InlineData(65)]
    public void ReaderRejectsInvalidGitObjectLengthsForCommitAndTree(int length)
    {
        Reject(Model(sourceCommit: new string('1', length)));
        Reject(Model(sourceTree: new string('2', length)));
        Assert.Throws<FormatException>(() => TruthExportValidation.RequireSameGitObjectFormat(
            new string('1', length),
            new string('2', length)));
    }

    [Fact]
    public void ReaderRejectsMixedGitObjectFormats()
    {
        Reject(Model(sourceCommit: Commit40, sourceTree: Tree64));
        Reject(Model(sourceCommit: Commit64, sourceTree: Tree40));
    }

    [Fact]
    public void ReaderRejectsUppercaseAndNonHexGitObjectIds()
    {
        Reject(Model(sourceCommit: new string('A', 40)));
        Reject(Model(sourceTree: new string('g', 40)));
    }

    [Theory]
    [InlineData("/A.lean")]
    [InlineData("A.lean/")]
    [InlineData("A/../B.lean")]
    [InlineData("A/./B.lean")]
    [InlineData("A//B.lean")]
    [InlineData("A\\B.lean")]
    [InlineData("A.txt")]
    [InlineData("")]
    public void ReaderRejectsInvalidRepoPaths(string repoPath) =>
        Reject(ModelOf(Node(repoPath, 'a')));

    [Fact]
    public void ReaderRejectsControlCharactersInRepoPaths() =>
        Reject(ModelOf(Node("A/\u001f/B.lean", 'a')));

    [Fact]
    public void ReaderRejectsMalformedFrozenAndStatementIds()
    {
        Reject(ModelOf(Node("A.lean", 'g')));
        Reject(ModelOf(Node("A.lean", 'a', statementId: "sha256:" + new string('A', 64))));
        Reject(ModelOf(Node("A.lean", 'a', statementId: "sha256:" + new string('1', 63))));
    }

    [Theory]
    [InlineData("lemma")]
    [InlineData("Theorem")]
    public void ReaderRejectsUnknownOrWrongCaseKinds(string kind) =>
        Reject(ModelOf(Node("A.lean", 'a', kind: kind)));

    [Fact]
    public void ReaderRejectsDuplicateRepoPathsEvenWhenFrozenIdsDiffer()
    {
        Reject(ModelOf(Node("A.lean", 'a'),
            Node("A.lean", 'b')));
    }

    [Fact]
    public void ReaderRejectsDuplicateFrozenIdsEvenWhenRepoPathsDiffer()
    {
        Reject(ModelOf(Node("A.lean", 'a'),
            Node("B.lean", 'a')));
    }

    [Fact]
    public void ReaderRejectsMissingPrerequisiteField()
    {
        var json = Encoding.UTF8.GetString(TruthExportJsonWriter.Write(ModelOf(Node("A.lean", 'a'))).AsSpan());
        var withoutRequiredField = json.Replace(
            ", \"prerequisite_frozen_node_ids\": []",
            string.Empty,
            StringComparison.Ordinal);
        Assert.NotEqual(json, withoutRequiredField);

        Assert.Throws<FormatException>(() =>
            TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(withoutRequiredField)));
    }

    [Fact]
    public void ReaderRejectsInvalidPrerequisiteId() =>
        Reject(ModelOf(Node("A.lean", 'a', prerequisites: new[] { "sha256:" + new string('g', 64) })));

    [Fact]
    public void ReaderRejectsUnsortedPrerequisites() =>
        Reject(ModelOf(Node("A.lean", 'a'),
            Node("B.lean", 'b'),
            Node("C.lean", 'c', prerequisites: new[] { Id('b'), Id('a') })));

    [Fact]
    public void ReaderRejectsDuplicatePrerequisites() =>
        Reject(ModelOf(Node("A.lean", 'a'),
            Node("B.lean", 'b', prerequisites: new[] { Id('a'), Id('a') })));

    [Fact]
    public void ReaderRejectsDanglingPrerequisiteEndpoint() =>
        Reject(ModelOf(Node("A.lean", 'a', prerequisites: new[] { Id('b') })));

    [Fact]
    public void ReaderRejectsSelfLoop() =>
        Reject(ModelOf(Node("A.lean", 'a', prerequisites: new[] { Id('a') })));

    [Fact]
    public void ReaderRejectsTwoNodeCycle() =>
        Reject(ModelOf(Node("A.lean", 'a', prerequisites: new[] { Id('b') }),
            Node("B.lean", 'b', prerequisites: new[] { Id('a') })));

    [Fact]
    public void ReaderRejectsLongerCycle() =>
        Reject(ModelOf(Node("A.lean", 'a', prerequisites: new[] { Id('c') }),
            Node("B.lean", 'b', prerequisites: new[] { Id('a') }),
            Node("C.lean", 'c', prerequisites: new[] { Id('b') })));

    [Fact]
    public void ReaderAcceptsValidMultiLevelDag()
    {
        var model = ModelOf(Node("A.lean", 'a'),
            Node("B.lean", 'b', prerequisites: new[] { Id('a') }),
            Node("C.lean", 'c', prerequisites: new[] { Id('a'), Id('b') }),
            Node("D.lean", 'd', prerequisites: new[] { Id('c') }));

        var actual = Read(model);

        Assert.Equal(4, actual.Nodes.Length);
        Assert.Equal(new[] { Id('a'), Id('b') }, actual.Nodes[2].PrerequisiteFrozenNodeIds);
    }

    [Fact]
    public void CreateCanonicalizesPrerequisitesBeforeSharedValidation()
    {
        var model = TruthExportModel.Create(
            ImmutableArray.Create(
                Node("C.lean", 'c', prerequisites: new[] { Id('b'), Id('a') }),
                Node("A.lean", 'a'),
                Node("B.lean", 'b', prerequisites: new[] { Id('a') })),
            Commit40,
            Tree40);

        Assert.Equal(new[] { Id('a'), Id('b') }, model.Nodes[2].PrerequisiteFrozenNodeIds);
    }

    [Fact]
    public void CreateRejectsAProducerModelTheReaderWouldReject()
    {
        Assert.Throws<FormatException>(() => TruthExportModel.Create(
            ImmutableArray.Create(Node("A.lean", 'a', prerequisites: new[] { Id('b') })),
            Commit40,
            Tree40));
        Assert.Throws<FormatException>(() => TruthExportModel.Create(
            ImmutableArray<TruthExportNode>.Empty,
            "not-a-git-object-id",
            Tree40));
    }

    // 独立名而非重载:ScribeTestMapDeriver 按 (TypeName, name) 解析本地调用,
    // 同名多目标即把每个调用者记为 unknown(SL-003 conservative unknown test method)。
    // 搬迁到本项目使这些方法成为新身份,故重载必须解开,否则 23 个方法全被 Block。
    private static TruthExportModel ModelOf(
        params TruthExportNode[] nodes) =>
        Model(nodes.ToImmutableArray());

    private static TruthExportModel Model(
        ImmutableArray<TruthExportNode> nodes = default,
        string sourceCommit = Commit40,
        string sourceTree = Tree40) =>
        new(
            TruthExportModel.SchemaName,
            1,
            TruthExportModel.CanonicalDialect,
            sourceCommit,
            sourceTree,
            TruthExportModel.ProducerName,
            nodes.IsDefault ? ImmutableArray<TruthExportNode>.Empty : nodes);

    private static TruthExportNode Node(
        string repoPath,
        char frozenId,
        string kind = "theorem",
        string? statementId = null,
        string[]? prerequisites = null) =>
        new(
            repoPath,
            Id(frozenId),
            ImmutableArray<string>.Empty,
            ImmutableArray.Create(new TruthExportDeclaration("nk-" + frozenId, kind, statementId ?? Id('1'))),
            (prerequisites ?? Array.Empty<string>()).ToImmutableArray());

    private static string Id(char value) => "sha256:" + new string(value, 64);

    private static TruthExportModel Read(TruthExportModel model) =>
        TruthExportJsonReader.Read(TruthExportJsonWriter.Write(model).AsSpan());

    private static void Reject(TruthExportModel model) =>
        Assert.Throws<FormatException>(() =>
            TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(UncheckedJson(model))));

    private static string UncheckedJson(TruthExportModel model) =>
        "{"
        + "\"schema\":" + JsonString(model.Schema)
        + ",\"schema_version\":" + model.SchemaVersion.ToString(CultureInfo.InvariantCulture)
        + ",\"dialect\":" + JsonString(model.Dialect)
        + ",\"source_commit\":" + JsonString(model.SourceCommit)
        + ",\"source_tree\":" + JsonString(model.SourceTree)
        + ",\"producer\":" + JsonString(model.Producer)
        + ",\"nodes\":[" + string.Join(',', model.Nodes.Select(UncheckedNodeJson)) + "]}"
        + "\n";

    private static string UncheckedNodeJson(TruthExportNode node) =>
        "{"
        + "\"repo_path\":" + JsonString(node.RepoPath)
        + ",\"frozen_node_id\":" + JsonString(node.FrozenNodeId)
        + ",\"node_axiom_closure\":["
        + string.Join(',', node.NodeAxiomClosure.Select(JsonString)) + "]"
        + ",\"declarations\":[" + string.Join(',', node.Declarations.Select(UncheckedDeclarationJson)) + "]"
        + ",\"prerequisite_frozen_node_ids\":["
        + string.Join(',', node.PrerequisiteFrozenNodeIds.Select(JsonString)) + "]}";

    private static string UncheckedDeclarationJson(TruthExportDeclaration declaration) =>
        "{"
        + "\"declaration_name_key\":" + JsonString(declaration.DeclarationNameKey)
        + ",\"kind\":" + JsonString(declaration.Kind)
        + ",\"statement_id\":" + JsonString(declaration.StatementId) + "}";

    private static string JsonString(string? value) => JsonSerializer.Serialize(value);
}
