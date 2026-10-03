using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceMaterializationTests
{
    [Fact]
    public void CodecRejectsClaimWithNullAuthoredStatementFormula() =>
        Reject(block => block["statementFormula"] = null, ScribeResourceErrorCode.ExtraField);

    [Fact]
    public void CodecRejectsNoFormulaWithNonemptyStatementFormula() =>
        Reject(block =>
        {
            block["statementSource"] = new JsonObject { ["type"] = "NoFormula" };
            block["statementFormula"] = Number(2);
        }, ScribeResourceErrorCode.ExtraField);

    [Fact]
    public void CodecRejectsAuthoredPresentationWithDifferentStatementFormula() =>
        Reject(block =>
        {
            block["claim"] = null;
            block["statementFormula"] = Number(2);
        }, ScribeResourceErrorCode.ExtraField);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CodecRejectsStatementSourceWithoutUnprojectableAssessment(bool noFormula) =>
        Reject(block =>
        {
            if (noFormula)
                block["statementSource"] = new JsonObject { ["type"] = "NoFormula" };
            block.Remove("assessment");
        }, ScribeResourceErrorCode.MissingField);

    [Theory]
    [InlineData("LeanDerived", true, true)]
    [InlineData("LeanDerived", false, false)]
    [InlineData("Authored", true, false)]
    [InlineData("Authored", false, true)]
    [InlineData("NoFormula", true, false)]
    [InlineData("NoFormula", false, true)]
    public void DecodingMatchesConstructionForEverySourceAndAssessment(string sourceKind, bool projected, bool legal)
    {
        var presentation = DefinitionDsl.Equal(DefinitionDsl.Num(1), DefinitionDsl.Num(1));
        var projection = DefinitionDsl.Equal(DefinitionDsl.Num(2), DefinitionDsl.Num(2));
        var source = sourceKind switch
        {
            "LeanDerived" => StatementSource.FromLean(),
            "Authored" => StatementSource.FromAuthor(presentation),
            "NoFormula" => StatementSource.WithoutFormula(),
            _ => throw new ArgumentOutOfRangeException(nameof(sourceKind)),
        };
        StatementAssessment assessment = projected
            ? new StatementAssessment.Projected(projection)
            : new StatementAssessment.Unprojectable("constant", "Fixture.subject", "fixture-projector", new string('c', 64));
        var definition = ScribeResourceCodecTests.ClaimDefinition();
        var resource = JsonNode.Parse(ScribeResourceCodec.Encode(definition))!;
        var construction = resource["document"]!["content"]![0]!["construction"]!.AsObject();
        construction["statementSource"] = new JsonObject { ["type"] = sourceKind };
        if (sourceKind == "Authored")
            construction["statementSource"]!["presentation"] = JsonNode.Parse("{\"type\":\"Relation\",\"left\":{\"type\":\"Number\",\"value\":1},\"operator\":\"Equal\",\"right\":{\"type\":\"Number\",\"value\":1}}");
        construction["assessment"] = projected
            ? new JsonObject { ["type"] = "Projected", ["formula"] = JsonNode.Parse(
                "{\"type\":\"Relation\",\"left\":{\"type\":\"Number\",\"value\":2},\"operator\":\"Equal\",\"right\":{\"type\":\"Number\",\"value\":2}}") }
            : new JsonObject
            {
                ["type"] = "Unprojectable", ["reasonCode"] = "constant", ["offendingSubject"] = "Fixture.subject",
                ["projectorEpoch"] = "fixture-projector", ["declarationContentDigest"] = new string('c', 64),
            };
        DocumentDefinition Construct()
        {
            var original = Assert.IsType<DocumentBlock.Describe>(definition.Document.Content.Items[0]);
            var describe = DocumentBlock.Describe.ReportDerived(original.Id, original.Title,
                DeclarationHandle.Create("D5/S1/Scale/Other.member"), source, original.AssessedProvenance,
                original.Content, DescribeRole.Theorem, original.OpenProblemResolutionClaim, recordedAssessment: assessment);
            return DocumentDefinition.Create(ScribeDocument.Create(definition.Document.Header, definition.Document.Title,
                DefinitionDsl.Blocks(describe), definition.Document.Edges), definition.SourcePath);
        }
        DocumentDefinition Decode() => ScribeResourceCodec.Decode(Encoding.UTF8.GetBytes(resource.ToJsonString()));
        if (!legal)
        {
            var expected = Assert.Throws<InvalidOperationException>(Construct);
            var actual = Assert.Throws<ScribeResourceException>(Decode);
            Assert.Equal(ScribeResourceErrorCode.InvalidValue, actual.ReasonCode);
            Assert.IsType<InvalidOperationException>(actual.InnerException);
            Assert.Equal(expected.Message, actual.InnerException!.Message);
            return;
        }
        var direct = Construct();
        using var root = new TemporaryRoot();
        var decoded = StatementProjectionFixtureLoader.WithRepositoryRoot(root.Path, Decode);
        Assert.True(ScribeResourceStructuralComparer.Equal(direct, decoded, out var difference), difference);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CodecRejectsRemovedGapField(bool noFormula) => Reject(block =>
    {
        if (noFormula) block["statementSource"] = new JsonObject { ["type"] = "NoFormula" };
        block["statementSource"]!["gap"] = null;
    }, ScribeResourceErrorCode.ExtraField);

    [Fact]
    public void CodecRejectsRemovedFormulaProvenanceField() => Reject(block =>
        block["statementFormulaProvenance"] = "HandAuthored", ScribeResourceErrorCode.ExtraField);

    [Fact]
    public void CodecRejectsPreviousSemanticVersion()
    {
        var resource = JsonNode.Parse(ScribeResourceCodec.Encode(ScribeResourceCodecTests.ClaimDefinition()))!;
        resource["version"] = 1;
        var error = Assert.Throws<ScribeResourceException>(() =>
            ScribeResourceCodec.Decode(Encoding.UTF8.GetBytes(resource.ToJsonString())));
        Assert.Equal(ScribeResourceErrorCode.VersionMismatch, error.ReasonCode);
        Assert.Equal(2, ScribeResourceCodec.SemanticVersion);
    }

    private static JsonObject Number(int value) => new() { ["type"] = "Number", ["value"] = value };

    private static void Reject(Action<JsonObject> change, ScribeResourceErrorCode reason)
    {
        var resource = JsonNode.Parse(ScribeResourceCodec.Encode(ScribeResourceCodecTests.ClaimDefinition()))!.AsObject();
        change(resource["document"]!["content"]![0]!["construction"]!.AsObject());
        var error = Assert.Throws<ScribeResourceException>(() =>
            ScribeResourceCodec.Decode(Encoding.UTF8.GetBytes(resource.ToJsonString())));
        Assert.Equal(reason, error.ReasonCode);
    }
}
