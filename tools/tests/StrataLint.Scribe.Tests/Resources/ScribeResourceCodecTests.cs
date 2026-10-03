using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceCodecTests
{
    public static IEnumerable<object[]> InvalidResources()
    {
        var valid = Encoding.UTF8.GetString(ScribeResourceCodec.Encode(Definition()));
        yield return [ScribeResourceErrorCode.InvalidUtf8, new byte[] { 0xff }];
        yield return [ScribeResourceErrorCode.InvalidJson, Encoding.UTF8.GetBytes("{")];
        yield return [ScribeResourceErrorCode.TrailingData, Encoding.UTF8.GetBytes(valid + "x")];
        yield return [ScribeResourceErrorCode.SchemaMismatch, Encoding.UTF8.GetBytes(valid.Replace(ScribeResourceCodec.SchemaName, "other", StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.VersionMismatch, Encoding.UTF8.GetBytes(valid.Replace($"\"version\":{ScribeResourceCodec.SemanticVersion}", "\"version\":0", StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.UnknownType, Encoding.UTF8.GetBytes(valid.Replace("\"type\":\"ScribeDocument\"", "\"type\":\"Unknown\"", StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.MissingField, Encoding.UTF8.GetBytes(valid.Replace(",\"sourcePath\":\"Blueprint/D5/S1/Scale/Resource.scribe.cs\"", string.Empty, StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.ExtraField, Encoding.UTF8.GetBytes(valid.Replace("}", ",\"extra\":0}", StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.TypeMismatch, Encoding.UTF8.GetBytes(valid.Replace($"\"version\":{ScribeResourceCodec.SemanticVersion}", "\"version\":\"one\"", StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.InvalidValue, Encoding.UTF8.GetBytes(valid.Replace("Blueprint/D5/S1/Scale/Resource.scribe.cs", "/tmp/resource.scribe.cs", StringComparison.Ordinal))];
    }

    [Fact]
    public void CodecRoundTripsDefinitionAndProducesStableUtf8()
    {
        var definition = DocumentDefinition.Create(
            ScribeNode.Create(
                "resource-digest",
                DefinitionDsl.H("Resource"),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("hello"))),
                sourcePath: "Blueprint/D5/S1/Scale/Resource.scribe.cs"),
            "Blueprint/D5/S1/Scale/Resource.scribe.cs");

        var encoded = ScribeResourceCodec.Encode(definition);
        var decoded = ScribeResourceCodec.Decode(encoded);

        Assert.Equal(encoded, ScribeResourceCodec.Encode(decoded));
        Assert.Equal("D5/S1/Scale/Resource", decoded.Document.Header.Gid.Value);
        Assert.Equal("Blueprint/D5/S1/Scale/Resource.scribe.cs", decoded.SourcePath);
    }

    [Fact]
    public void CodecRejectsUnknownTypeWithNamedReason()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "{\"schema\":\"trureturing.scribe.document-definition\",\"version\":2,\"document\":{\"type\":\"unknown\"},\"sourcePath\":\"Blueprint/D5/S1/Resource.scribe.cs\"}");

        var error = Assert.Throws<ScribeResourceException>(() => ScribeResourceCodec.Decode(bytes));

        Assert.Equal(ScribeResourceErrorCode.UnknownType, error.ReasonCode);
    }

    [Fact]
    public void EveryMalformedResourceFailsClosed()
    {
        foreach (var item in InvalidResources())
        {
            var expected = (ScribeResourceErrorCode)item[0];
            var bytes = (byte[])item[1];
            var error = Assert.Throws<ScribeResourceException>(() => ScribeResourceCodec.Decode(bytes));

            Assert.Equal(expected, error.ReasonCode);
        }
    }

    [Fact]
    public void ExpectedIdentityMismatchUsesTheSameNamedException()
    {
        var bytes = ScribeResourceCodec.Encode(Definition());

        var error = Assert.Throws<ScribeResourceException>(() =>
            ScribeResourceCodec.Decode(bytes, expectedGid: "D5/S1/Scale/Other"));

        Assert.Equal(ScribeResourceErrorCode.ExpectationMismatch, error.ReasonCode);
    }

    [Fact]
    public void ClaimMembersSurviveRoundTrip()
    {
        var encoded = ScribeResourceCodec.Encode(ClaimDefinition());
        var decoded = ScribeResourceCodec.Decode(encoded);

        Assert.Equal(encoded, ScribeResourceCodec.Encode(decoded));
        Assert.Contains("\"additionalMembers\":[\"D5/S1/Scale/Other.additional\"]", Encoding.UTF8.GetString(encoded), StringComparison.Ordinal);
    }

    [Fact]
    public void CodecRejectsAuthoredFormulaWithDeclarationOnlyKind()
    {
        var resource = JsonNode.Parse(ScribeResourceCodec.Encode(AuthoredFormulaDefinition()))!.AsObject();
        var block = resource["document"]!["content"]![0]!.AsObject();
        block["construction"]!["kind"] = "Theorem";

        var error = Assert.Throws<ScribeResourceException>(() =>
            ScribeResourceCodec.Decode(Encoding.UTF8.GetBytes(resource.ToJsonString())));

        Assert.Equal(ScribeResourceErrorCode.InvalidValue, error.ReasonCode);
    }

    [Fact]
    public void CodecRejectsMismatchedDeclarationHandleAndStatement()
    {
        var resource = JsonNode.Parse(ScribeResourceCodec.Encode(ClaimDefinition()))!.AsObject();
        var block = resource["document"]!["content"]![0]!.AsObject();
        block["construction"]!["statement"] = new JsonObject
        {
            ["type"] = "LeanDeclaration", ["value"] = "D5/S1/Scale/Other.different",
        };

        var error = Assert.Throws<ScribeResourceException>(() =>
            ScribeResourceCodec.Decode(Encoding.UTF8.GetBytes(resource.ToJsonString())));

        Assert.Equal(ScribeResourceErrorCode.ExtraField, error.ReasonCode);
    }

    [Fact]
    public void CodecRejectsDuplicateTopLevelField()
    {
        var valid = Encoding.UTF8.GetString(ScribeResourceCodec.Encode(Definition()));
        var version = $"\"version\":{ScribeResourceCodec.SemanticVersion}";
        var duplicate = valid.Replace(version, version + "," + version, StringComparison.Ordinal);

        var error = Assert.Throws<ScribeResourceException>(() =>
            ScribeResourceCodec.Decode(Encoding.UTF8.GetBytes(duplicate)));

        Assert.Equal(ScribeResourceErrorCode.DuplicateField, error.ReasonCode);
    }

    [Fact]
    public void CodecRejectsDuplicateNestedField()
    {
        var valid = Encoding.UTF8.GetString(ScribeResourceCodec.Encode(ClaimDefinition()));
        var duplicate = valid.Replace(
            "\"handle\":\"D5/S1/Scale/Other.member\"",
            "\"handle\":\"D5/S1/Scale/Other.member\",\"handle\":\"D5/S1/Scale/Other.member\"",
            StringComparison.Ordinal);

        var error = Assert.Throws<ScribeResourceException>(() =>
            ScribeResourceCodec.Decode(Encoding.UTF8.GetBytes(duplicate)));

        Assert.Equal(ScribeResourceErrorCode.DuplicateField, error.ReasonCode);
    }

    [Theory]
    [InlineData("formula")]
    [InlineData("remark")]
    [InlineData("handle")]
    public void CodecRejectsResolutionClaimOutsideItsLeanDeclarationFactory(string invalidHost)
    {
        var resource = JsonNode.Parse(ScribeResourceCodec.Encode(ClaimDefinition()))!.AsObject();
        var block = resource["document"]!["content"]![0]!.AsObject();
        var construction = block["construction"]!.AsObject();
        if (invalidHost == "formula")
        {
            block["construction"] = new JsonObject
            {
                ["type"] = "AuthoredFormula", ["kind"] = "Remark",
                ["formula"] = construction["statementSource"]!["presentation"]!.DeepClone(),
                ["claim"] = construction["claim"]!.DeepClone(),
            };
        }
        else if (invalidHost == "remark")
        {
            construction["role"] = "Remark";
        }
        else
        {
            construction["statement"] = new JsonObject
            {
                ["type"] = "LeanDeclaration", ["value"] = "D5/S1/Scale/Other.different",
            };
        }

        var error = Assert.Throws<ScribeResourceException>(() =>
            ScribeResourceCodec.Decode(Encoding.UTF8.GetBytes(resource.ToJsonString())));

        Assert.Equal(invalidHost == "remark" ? ScribeResourceErrorCode.InvalidValue : ScribeResourceErrorCode.ExtraField,
            error.ReasonCode);
    }

    internal static DocumentDefinition ClaimDefinition()
    {
        var formula = DefinitionDsl.Equal(DefinitionDsl.Num(1), DefinitionDsl.Num(1));
        var source = StatementSource.FromAuthor(formula);
        var describe = DocumentBlock.Describe.ReportDerived(
            DescribeId.Create("claim"), DefinitionDsl.H("Claim"),
            DeclarationHandle.Create("D5/S1/Scale/Other.member"), source,
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("claim"))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("batch-problem"), ResolutionKind.Proved,
                [DeclarationHandle.Create("D5/S1/Scale/Other.additional")]),
            recordedAssessment: new StatementAssessment.Unprojectable(
                "missing", "D5/S1/Scale/Other.member", "statement-projector-v1", new string('a', 64)));
        return DocumentDefinition.Create(
            ScribeNode.Create("resource-digest", DefinitionDsl.H("Claim"), DefinitionDsl.Blocks(describe),
                sourcePath: "Blueprint/D5/S1/Scale/Claim.scribe.cs"),
            "Blueprint/D5/S1/Scale/Claim.scribe.cs");
    }

    private static DocumentDefinition AuthoredFormulaDefinition()
    {
        var describe = Describe.Remark(
            DescribeId.Create("authored"),
            DefinitionDsl.H("Authored"),
            DefinitionDsl.Equal(DefinitionDsl.Num(1), DefinitionDsl.Num(1)),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("authored"))));
        return DocumentDefinition.Create(
            ScribeNode.Create("resource-digest", DefinitionDsl.H("Authored"), DefinitionDsl.Blocks(describe),
                sourcePath: "Blueprint/D5/S1/Scale/Authored.scribe.cs"),
            "Blueprint/D5/S1/Scale/Authored.scribe.cs");
    }

    [Fact]
    public void LeanDerivedFormulaAndAssessmentSurviveRoundTrip()
    {
        var describe = DocumentBlock.Describe.ReportDerived(
            DescribeId.Create("derived"), DefinitionDsl.H("Derived"),
            DeclarationHandle.Create("D5/S1/Scale/Other.member"), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("derived"))),
            DescribeRole.Theorem, null,
            recordedAssessment: new StatementAssessment.Projected(DefinitionDsl.Equal(DefinitionDsl.Num(1), DefinitionDsl.Num(1))));
        var definition = DocumentDefinition.Create(
            ScribeNode.Create("resource-digest", DefinitionDsl.H("Derived"), DefinitionDsl.Blocks(describe),
                sourcePath: "Blueprint/D5/S1/Scale/Derived.scribe.cs"),
            "Blueprint/D5/S1/Scale/Derived.scribe.cs");

        var decoded = ScribeResourceCodec.Decode(ScribeResourceCodec.Encode(definition));
        var restored = Assert.IsType<DocumentBlock.Describe>(decoded.Document.Content.Items[0]);
        Assert.Equal(StatementFormulaProvenance.LeanDerived, restored.FormulaProvenance);
        Assert.True(ScribeResourceStructuralComparer.Equal(definition, decoded, out var difference), difference);
    }

    private static DocumentDefinition Definition() => DocumentDefinition.Create(
        ScribeNode.Create(
            "resource-digest",
            DefinitionDsl.H("Resource"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("hello"))),
            sourcePath: "Blueprint/D5/S1/Scale/Resource.scribe.cs"),
        "Blueprint/D5/S1/Scale/Resource.scribe.cs");
}
