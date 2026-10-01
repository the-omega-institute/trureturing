using System.Text;
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
        yield return [ScribeResourceErrorCode.VersionMismatch, Encoding.UTF8.GetBytes(valid.Replace("\"version\":1", "\"version\":2", StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.UnknownType, Encoding.UTF8.GetBytes(valid.Replace("\"type\":\"ScribeDocument\"", "\"type\":\"Unknown\"", StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.MissingField, Encoding.UTF8.GetBytes(valid.Replace(",\"sourcePath\":\"Blueprint/D5/S1/Scale/Resource.scribe.cs\"", string.Empty, StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.ExtraField, Encoding.UTF8.GetBytes(valid.Replace("}", ",\"extra\":0}", StringComparison.Ordinal))];
        yield return [ScribeResourceErrorCode.TypeMismatch, Encoding.UTF8.GetBytes(valid.Replace("\"version\":1", "\"version\":\"one\"", StringComparison.Ordinal))];
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
            "{\"schema\":\"trureturing.scribe.document-definition\",\"version\":1,\"document\":{\"type\":\"unknown\"},\"sourcePath\":\"Blueprint/D5/S1/Resource.scribe.cs\"}");

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
        var claim = new OpenProblemResolutionClaim(
            ProblemSlugRef.Create("batch-problem"),
            ResolutionKind.Proved,
            [DeclarationHandle.Create("D5/S1/Scale/Other.member")]);
        var document = ScribeNode.Create(
            "resource-digest",
            DefinitionDsl.H("Claim"),
            DefinitionDsl.Blocks(DocumentBlock.Describe.Restore(
                DescribeId.Create("claim"),
                DefinitionDsl.H("Claim"),
                DescribeStatement.FromFormula(DefinitionDsl.Equal(DefinitionDsl.Num(1), DefinitionDsl.Num(1))),
                AssessedProvenance.FromRepo(),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("claim"))),
                null,
                null,
                claim,
                new DescribeKindSource.Authored(DescribeKind.Remark))),
            sourcePath: "Blueprint/D5/S1/Scale/Claim.scribe.cs");

        var encoded = ScribeResourceCodec.Encode(DocumentDefinition.Create(document, "Blueprint/D5/S1/Scale/Claim.scribe.cs"));
        var decoded = ScribeResourceCodec.Decode(encoded);

        Assert.Equal(encoded, ScribeResourceCodec.Encode(decoded));
        Assert.Contains("\"additionalMembers\":[\"D5/S1/Scale/Other.member\"]", Encoding.UTF8.GetString(encoded), StringComparison.Ordinal);
    }

    [Fact]
    public void LeanDerivedFormulaMarkerSurvivesRoundTripWhenSourceIsImplicit()
    {
        var declaration = LeanDeclarationRef.Create("D5/S1/Scale/Other.member");
        var formula = DefinitionDsl.Equal(DefinitionDsl.Num(1), DefinitionDsl.Num(1));
        StatementProjectionFixtureLoader.RestoreDerived(formula, declaration);
        var describe = DocumentBlock.Describe.Restore(
            DescribeId.Create("derived"),
            DefinitionDsl.H("Derived"),
            DescribeStatement.FromLean(declaration),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("derived"))),
            formula,
            null,
            null,
            new DescribeKindSource.Authored(DescribeKind.Remark));
        var definition = DocumentDefinition.Create(
            ScribeNode.Create(
                "resource-digest",
                DefinitionDsl.H("Derived"),
                DefinitionDsl.Blocks(describe),
                sourcePath: "Blueprint/D5/S1/Scale/Derived.scribe.cs"),
            "Blueprint/D5/S1/Scale/Derived.scribe.cs");

        var decoded = ScribeResourceCodec.Decode(ScribeResourceCodec.Encode(definition));
        var restored = Assert.IsType<DocumentBlock.Describe>(decoded.Document.Content.Items[0]);
        Assert.Equal(StatementFormulaProvenance.LeanDerived, restored.FormulaProvenance);
        Assert.True(StatementProjectionFixtureLoader.IsDerivedFrom(restored.StatementFormula!, declaration));
    }

    private static DocumentDefinition Definition() => DocumentDefinition.Create(
        ScribeNode.Create(
            "resource-digest",
            DefinitionDsl.H("Resource"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("hello"))),
            sourcePath: "Blueprint/D5/S1/Scale/Resource.scribe.cs"),
        "Blueprint/D5/S1/Scale/Resource.scribe.cs");
}
