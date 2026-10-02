using System.Text.Json;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe;

public static partial class ScribeResourceCodec
{
    private static JsonObject WriteDescribe(DocumentBlock.Describe value) => Obj(
        "type", "Describe", "id", value.Id.Value, "title", value.Title.Value,
        "provenance", WriteProvenance(value.AssessedProvenance), "content", WriteBlocks(value.Content),
        "construction", WriteDescribeConstruction(value));

    private static JsonObject WriteDescribeConstruction(DocumentBlock.Describe value) => value.KindSource switch
    {
        DescribeKindSource.Authored authored when value.Statement is DescribeStatement.FormulaAst formula =>
            Obj("type", "AuthoredFormula", "kind", authored.Value.ToString(), "formula", WriteFormula(formula.Value)),
        DescribeKindSource.ReportDerived { Role: DescribeRole.Remark } derived =>
            Obj("type", "DeclarationRemark", "handle", derived.Handle.Value),
        DescribeKindSource.ReportDerived derived => Obj(
            "type", "ReportDerived", "handle", derived.Handle.Value, "role", derived.Role?.ToString(),
            "statementSource", WriteStatementSource(value.StatementSource ?? throw Invalid("Missing statement source.")),
            "assessment", WriteAssessment(value.StatementAssessment ?? throw Invalid("Missing statement assessment.")),
            "claim", value.OpenProblemResolutionClaim is null ? null : WriteClaim(value.OpenProblemResolutionClaim)),
        _ => throw Invalid("Unknown Describe construction."),
    };

    private static DocumentBlock.Describe ReadDescribe(JsonObject value)
    {
        var obj = Typed(value, "Describe", "id", "title", "provenance", "content", "construction");
        var id = DescribeId.Create(ReadString(obj, "id"));
        var title = Heading.Create(ReadString(obj, "title"));
        var provenance = ReadProvenance(obj, "provenance");
        var content = ReadBlocks(obj, "content");
        var construction = RequireObject(Element(obj).GetProperty("construction"));
        return ReadType(construction) switch
        {
            "AuthoredFormula" => ReadTyped(construction, "AuthoredFormula", "kind", "formula", () =>
                DocumentBlock.Describe.AuthoredFormula(id, ParseEnum<DescribeKind>(construction, "kind"), title,
                    ReadFormula(construction, "formula"), provenance, content)),
            "DeclarationRemark" => ReadTyped(construction, "DeclarationRemark", "handle", () =>
                DocumentBlock.Describe.RemarkOn(id, DeclarationHandle.Create(ReadString(construction, "handle")),
                    title, provenance, content)),
            "ReportDerived" => ReadTyped(construction, "ReportDerived", () =>
                DocumentBlock.Describe.ReportDerived(id, title,
                    DeclarationHandle.Create(ReadString(construction, "handle")),
                    ReadStatementSource(construction, "statementSource"), provenance, content,
                    ReadNullableEnum<DescribeRole>(construction, "role"), ReadNullableClaim(construction, "claim"),
                    recordedAssessment: ReadAssessment(construction, "assessment")),
                "handle", "role", "statementSource", "assessment", "claim"),
            _ => throw UnknownType(construction),
        };
    }

    private static JsonObject WriteStatementSource(StatementSource value) => value switch
    {
        StatementSource.LeanDerived => Obj("type", "LeanDerived"),
        StatementSource.Authored authored => Obj("type", "Authored", "presentation", WriteFormula(authored.Presentation)),
        StatementSource.NoFormula => Obj("type", "NoFormula"),
        _ => throw Unknown(value),
    };

    private static StatementSource ReadStatementSource(JsonObject parent, string name)
    {
        var obj = RequireObject(Element(parent).GetProperty(name));
        return ReadType(obj) switch
        {
            "LeanDerived" => ReadTyped(obj, "LeanDerived", () => StatementSource.FromLean()),
            "Authored" => ReadTyped(obj, "Authored", "presentation", () => StatementSource.FromAuthor(ReadFormula(obj, "presentation"))),
            "NoFormula" => ReadTyped(obj, "NoFormula", () => StatementSource.WithoutFormula()),
            _ => throw UnknownType(obj),
        };
    }

    private static JsonObject WriteAssessment(StatementAssessment value) => value switch
    {
        StatementAssessment.Projected projected => Obj("type", "Projected", "formula", WriteFormula(projected.Formula)),
        StatementAssessment.Unprojectable failed => Obj("type", "Unprojectable",
            "reasonCode", failed.ReasonCode, "offendingSubject", failed.OffendingSubject,
            "projectorEpoch", failed.ProjectorEpoch, "declarationContentDigest", failed.DeclarationContentDigest),
        _ => throw Unknown(value),
    };

    private static StatementAssessment ReadAssessment(JsonObject parent, string name)
    {
        var obj = RequireObject(Element(parent).GetProperty(name));
        return ReadType(obj) switch
        {
            "Projected" => ReadTyped(obj, "Projected", "formula", () =>
                new StatementAssessment.Projected(ReadFormula(obj, "formula"))),
            "Unprojectable" => ReadTyped(obj, "Unprojectable", "reasonCode", "offendingSubject", "projectorEpoch", "declarationContentDigest", () =>
                new StatementAssessment.Unprojectable(ReadString(obj, "reasonCode"), ReadString(obj, "offendingSubject"),
                    ReadString(obj, "projectorEpoch"), ReadString(obj, "declarationContentDigest"))),
            _ => throw UnknownType(obj),
        };
    }
}
