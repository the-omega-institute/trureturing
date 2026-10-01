using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public enum ScribeResourceErrorCode
{
    InvalidUtf8,
    InvalidJson,
    TrailingData,
    SchemaMismatch,
    VersionMismatch,
    UnknownType,
    MissingField,
    ExtraField,
    TypeMismatch,
    InvalidValue,
    ExpectationMismatch,
}

public sealed class ScribeResourceException : FormatException
{
    public ScribeResourceException(ScribeResourceErrorCode reasonCode, string message, Exception? inner = null)
        : base($"{reasonCode}: {message}", inner) => ReasonCode = reasonCode;

    public ScribeResourceErrorCode ReasonCode { get; }
}

public static partial class ScribeResourceCodec
{
    public const string SchemaName = "trureturing.scribe.document-definition";
    public const int SemanticVersion = 1;

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        Encoder = System.Text.Encodings.Web.JavaScriptEncoder.Default,
        MaxDepth = 1024,
        WriteIndented = false,
    };

    private static readonly JsonDocumentOptions JsonParseOptions = new()
    {
        AllowTrailingCommas = false,
        CommentHandling = JsonCommentHandling.Disallow,
        MaxDepth = 1024,
    };

    public static byte[] Encode(DocumentDefinition definition)
    {
        ArgumentNullException.ThrowIfNull(definition);
        try
        {
            var root = new JsonObject
            {
                ["schema"] = SchemaName,
                ["version"] = SemanticVersion,
                ["document"] = WriteDocument(definition.Document),
                ["sourcePath"] = RelativeSourcePath(definition.SourcePath),
            };
            return JsonSerializer.SerializeToUtf8Bytes(root, JsonOptions);
        }
        catch (ScribeResourceException)
        {
            throw;
        }
        catch (Exception exception) when (exception is ArgumentException or InvalidOperationException)
        {
            throw new ScribeResourceException(ScribeResourceErrorCode.InvalidValue, exception.Message, exception);
        }
    }

    public static DocumentDefinition Decode(
        ReadOnlySpan<byte> bytes,
        string? expectedGid = null,
        string? expectedSourcePath = null)
    {
        string text;
        try
        {
            text = new UTF8Encoding(false, true).GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new ScribeResourceException(ScribeResourceErrorCode.InvalidUtf8, "Resource is not valid UTF-8.", exception);
        }

        JsonDocument document;
        try
        {
            document = JsonDocument.Parse(text, JsonParseOptions);
        }
        catch (JsonException exception)
        {
            var lastClose = text.LastIndexOf('}');
            var code = lastClose >= 0 && text[(lastClose + 1)..].Trim().Length != 0
                ? ScribeResourceErrorCode.TrailingData
                : ScribeResourceErrorCode.InvalidJson;
            throw new ScribeResourceException(code, "Resource JSON is not a single valid document.", exception);
        }

        try
        {
            using (document)
            {
                var root = document.RootElement;
                RequireFields(root, "schema", "version", "document", "sourcePath");
                var schema = ReadString(root, "schema");
                if (!string.Equals(schema, SchemaName, StringComparison.Ordinal))
                {
                    throw new ScribeResourceException(ScribeResourceErrorCode.SchemaMismatch, $"Expected schema '{SchemaName}'.");
                }

                if (ReadInt(root, "version") != SemanticVersion)
                {
                    throw new ScribeResourceException(ScribeResourceErrorCode.VersionMismatch, $"Expected semantic version {SemanticVersion}.");
                }

                var sourcePath = ReadRelativeSourcePath(root, "sourcePath");
                var decoded = DocumentDefinition.Create(ReadDocument(root.GetProperty("document")), sourcePath);
                if (expectedGid is not null && !string.Equals(expectedGid, decoded.Document.Header.Gid.Value, StringComparison.Ordinal))
                {
                    throw new ScribeResourceException(ScribeResourceErrorCode.ExpectationMismatch, "Expected GID does not match resource content.");
                }

                if (expectedSourcePath is not null
                    && !string.Equals(RelativeSourcePath(expectedSourcePath), sourcePath, StringComparison.Ordinal))
                {
                    throw new ScribeResourceException(ScribeResourceErrorCode.ExpectationMismatch, "Expected source path does not match resource content.");
                }

                return decoded;
            }
        }
        catch (ScribeResourceException)
        {
            throw;
        }
        catch (Exception exception) when (exception is ArgumentException or InvalidOperationException or FormatException or JsonException)
        {
            throw new ScribeResourceException(ScribeResourceErrorCode.InvalidValue, exception.Message, exception);
        }
    }

    public static DocumentDefinition Decode(byte[] bytes, string? expectedGid = null, string? expectedSourcePath = null) =>
        Decode(bytes.AsSpan(), expectedGid, expectedSourcePath);

    private static string RelativeSourcePath(string sourcePath)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(sourcePath);
        var normalized = sourcePath.Replace('\\', '/');
        var marker = normalized.LastIndexOf("/Blueprint/", StringComparison.Ordinal);
        if (marker >= 0)
        {
            return normalized[(marker + 1)..];
        }

        return normalized.StartsWith("Blueprint/", StringComparison.Ordinal)
            ? normalized
            : throw new ScribeResourceException(ScribeResourceErrorCode.InvalidValue, "Source path must be repository-relative under Blueprint/.");
    }

    private static string ReadRelativeSourcePath(JsonElement parent, string name)
    {
        var value = ReadString(parent, name).Replace('\\', '/');
        if (!value.StartsWith("Blueprint/", StringComparison.Ordinal)
            || value.Contains("../", StringComparison.Ordinal)
            || value.Contains("/..", StringComparison.Ordinal))
        {
            throw new ScribeResourceException(ScribeResourceErrorCode.InvalidValue, "Source path must be repository-relative under Blueprint/.");
        }

        return value;
    }

    private static JsonObject WriteDocument(ScribeDocument value) =>
        Obj("type", "ScribeDocument", "header", WriteHeader(value.Header), "title", value.Title.Value, "content", WriteBlocks(value.Content), "edges", new JsonArray(value.Edges.Select(WriteEdge).ToArray()));

    private static ScribeDocument ReadDocument(JsonElement value)
    {
        var obj = Typed(value, "ScribeDocument", "header", "title", "content", "edges");
        return ScribeDocument.Create(ReadHeader(obj, "header"), Heading.Create(ReadString(obj, "title")), ReadBlocks(obj, "content"), ReadArray(obj, "edges").EnumerateArray().Select(ReadEdge));
    }

    private static JsonObject WriteHeader(DocumentHeader value) =>
        Obj("type", "DocumentHeader", "gid", value.Gid.Value, "generality", value.Generality.ToString(), "mirrorBlueprint", value.MirrorBlueprint.Value, "mirrorEvidence", WriteEvidence(value.MirrorEvidence), "anchors", new JsonArray(value.Anchors.Select(static item => JsonValue.Create(item.CanonicalString)).ToArray()), "digest", value.Digest.Value);

    private static DocumentHeader ReadHeader(JsonElement parent, string name)
    {
        var obj = Typed(parent.GetProperty(name), "DocumentHeader", "gid", "generality", "mirrorBlueprint", "mirrorEvidence", "anchors", "digest");
        return DocumentHeader.Create(
            GidRef.Create(ReadString(obj, "gid")),
            ParseEnum<Generality>(obj, "generality"),
            GidRef.Create(ReadString(obj, "mirrorBlueprint")),
            ReadEvidence(obj, "mirrorEvidence"),
            ReadArray(obj, "anchors").EnumerateArray().Select(item => Anchor.ParseCanonical(ReadRequiredString(item, "anchor"))),
            Digest.Create(ReadString(obj, "digest")));
    }

    private static DocumentHeader ReadHeader(JsonObject parent, string name) => ReadHeader(Element(parent), name);

    private static JsonObject WriteEvidence(EvidenceMirror value) => value switch
    {
        EvidenceMirror.Artifact artifact => Obj("type", "Artifact", "reference", artifact.Reference.Value),
        EvidenceMirror.Waiver waiver => Obj("type", "Waiver", "reason", waiver.Reason.Value),
        _ => throw Unknown(value),
    };

    private static EvidenceMirror ReadEvidence(JsonElement parent, string name)
    {
        var obj = RequireObject(parent.GetProperty(name));
        return ReadType(obj) switch
        {
            "Artifact" => ReadTyped(obj, "Artifact", "reference", () => new EvidenceMirror.Artifact(GidRef.Create(ReadString(obj, "reference")))),
            "Waiver" => ReadTyped(obj, "Waiver", "reason", () => new EvidenceMirror.Waiver(WaiverReason.Create(ReadString(obj, "reason")))),
            _ => throw UnknownType(obj),
        };
    }

    private static EvidenceMirror ReadEvidence(JsonObject parent, string name) => ReadEvidence(Element(parent), name);

    private static JsonArray WriteBlocks(BlockSequence value) => new(value.Items.Select(WriteBlock).ToArray());

    private static BlockSequence ReadBlocks(JsonElement parent, string name) =>
        BlockSequence.Create(ReadArray(parent, name).EnumerateArray().Select(ReadBlock));

    private static BlockSequence ReadBlocks(JsonObject parent, string name) => ReadBlocks(Element(parent), name);

    private static JsonObject WriteBlock(DocumentBlock value) => value switch
    {
        DocumentBlock.Paragraph paragraph => Obj("type", "Paragraph", "content", WriteInlineSequence(paragraph.Content)),
        DocumentBlock.DisplayFormula formula => Obj("type", "DisplayFormula", "value", WriteFormula(formula.Value)),
        DocumentBlock.Section section => Obj("type", "Section", "title", section.Title.Value, "content", WriteBlocks(section.Content)),
        DocumentBlock.Describe describe => WriteDescribe(describe),
        _ => throw Unknown(value),
    };

    private static DocumentBlock ReadBlock(JsonElement value)
    {
        var obj = RequireObject(value);
        return ReadType(obj) switch
        {
            "Paragraph" => ReadTyped(obj, "Paragraph", "content", () => new DocumentBlock.Paragraph(ReadInlineSequence(obj, "content"))),
            "DisplayFormula" => ReadTyped(obj, "DisplayFormula", "value", () => new DocumentBlock.DisplayFormula(ReadFormula(obj, "value"))),
            "Section" => ReadTyped(obj, "Section", "title", "content", () => new DocumentBlock.Section(Heading.Create(ReadString(obj, "title")), ReadBlocks(obj, "content"))),
            "Describe" => ReadDescribe(obj),
            _ => throw UnknownType(obj),
        };
    }

    private static JsonArray WriteInlineSequence(InlineSequence value) => new(value.Items.Select(WriteInline).ToArray());

    private static InlineSequence ReadInlineSequence(JsonElement parent, string name) =>
        InlineSequence.Create(ReadArray(parent, name).EnumerateArray().Select(ReadInline));

    private static InlineSequence ReadInlineSequence(JsonObject parent, string name) => ReadInlineSequence(Element(parent), name);

    private static JsonObject WriteInline(Inline value) => value switch
    {
        Inline.Text text => Obj("type", "Text", "value", text.Run.Value),
        Inline.InlineFormula formula => Obj("type", "InlineFormula", "value", WriteFormula(formula.Value)),
        Inline.GidReference reference => Obj("type", "GidReference", "value", reference.Reference.Value),
        _ => throw Unknown(value),
    };

    private static Inline ReadInline(JsonElement value)
    {
        var obj = RequireObject(value);
        return ReadType(obj) switch
        {
            "Text" => ReadTyped(obj, "Text", "value", () => new Inline.Text(TextRun.Create(ReadString(obj, "value")))),
            "InlineFormula" => ReadTyped(obj, "InlineFormula", "value", () => new Inline.InlineFormula(ReadFormula(obj, "value"))),
            "GidReference" => ReadTyped(obj, "GidReference", "value", () => new Inline.GidReference(GidRef.Create(ReadString(obj, "value")))),
            _ => throw UnknownType(obj),
        };
    }

    private static JsonObject WriteDescribe(DocumentBlock.Describe value) => Obj(
        "type", "Describe",
        "id", value.Id.Value,
        "title", value.Title.Value,
        "statement", WriteStatement(value.Statement),
        "kindSource", WriteKindSource(value.KindSource),
        "provenance", WriteProvenance(value.AssessedProvenance),
        "content", WriteBlocks(value.Content),
        "statementFormula", value.StatementFormula is null ? null : WriteFormula(value.StatementFormula),
        "statementFormulaProvenance", value.FormulaProvenance.ToString(),
        "statementSource", value.StatementSource is null ? null : WriteStatementSource(value.StatementSource),
        "claim", value.OpenProblemResolutionClaim is null ? null : WriteClaim(value.OpenProblemResolutionClaim));

    private static JsonObject WriteStatement(DescribeStatement value) => value switch
    {
        DescribeStatement.FormulaAst formula => Obj("type", "FormulaAst", "value", WriteFormula(formula.Value)),
        DescribeStatement.LeanDeclaration lean => Obj("type", "LeanDeclaration", "value", lean.Value.Value),
        _ => throw Unknown(value),
    };

    private static DescribeStatement ReadStatement(JsonElement parent, string name)
    {
        var obj = RequireObject(parent.GetProperty(name));
        return ReadType(obj) switch
        {
            "FormulaAst" => ReadTyped(obj, "FormulaAst", "value", () => DescribeStatement.FromFormula(ReadFormula(obj, "value"))),
            "LeanDeclaration" => ReadTyped(obj, "LeanDeclaration", "value", () => DescribeStatement.FromLean(LeanDeclarationRef.Create(ReadString(obj, "value")))),
            _ => throw UnknownType(obj),
        };
    }

    private static DescribeStatement ReadStatement(JsonObject parent, string name) => ReadStatement(Element(parent), name);

    private static JsonObject WriteKindSource(DescribeKindSource value) => value switch
    {
        DescribeKindSource.Authored authored => Obj("type", "Authored", "kind", authored.Value.ToString()),
        DescribeKindSource.ReportDerived derived => Obj("type", "ReportDerived", "handle", derived.Handle.Value, "role", derived.Role?.ToString()),
        _ => throw Unknown(value),
    };

    private static DescribeKindSource ReadKindSource(JsonElement parent, string name)
    {
        var obj = RequireObject(parent.GetProperty(name));
        return ReadType(obj) switch
        {
            "Authored" => ReadTyped(obj, "Authored", "kind", () => new DescribeKindSource.Authored(ParseEnum<DescribeKind>(obj, "kind"))),
            "ReportDerived" => ReadTyped(obj, "ReportDerived", "handle", "role", () => new DescribeKindSource.ReportDerived(DeclarationHandle.Create(ReadString(obj, "handle")), ReadNullableEnum<DescribeRole>(obj, "role"))),
            _ => throw UnknownType(obj),
        };
    }

    private static DescribeKindSource ReadKindSource(JsonObject parent, string name) => ReadKindSource(Element(parent), name);

    private static JsonObject WriteStatementSource(StatementSource value) => value switch
    {
        StatementSource.LeanDerived => Obj("type", "LeanDerived"),
        StatementSource.Authored authored => Obj("type", "Authored", "presentation", WriteFormula(authored.Presentation), "gap", WriteNullableGap(authored.ProjectionGap)),
        StatementSource.NoFormula noFormula => Obj("type", "NoFormula", "gap", WriteNullableGap(noFormula.ProjectionGap)),
        _ => throw Unknown(value),
    };

    private static StatementSource? ReadNullableStatementSource(JsonElement parent, string name)
    {
        var element = parent.GetProperty(name);
        if (element.ValueKind == JsonValueKind.Null) return null;
        var obj = RequireObject(element);
        return ReadType(obj) switch
        {
            "LeanDerived" => ReadTyped(obj, "LeanDerived", () => StatementSource.FromLean()),
            "Authored" => ReadTyped(obj, "Authored", "presentation", "gap", () => new StatementSource.Authored(ReadFormula(obj, "presentation"), ReadNullableGap(obj, "gap"))),
            "NoFormula" => ReadTyped(obj, "NoFormula", "gap", () => new StatementSource.NoFormula(ReadNullableGap(obj, "gap"))),
            _ => throw UnknownType(obj),
        };
    }

    private static StatementSource? ReadNullableStatementSource(JsonObject parent, string name) => ReadNullableStatementSource(Element(parent), name);

    private static JsonNode? WriteNullableGap(ProjectionGap? value) => value is null ? null : Obj("type", "ProjectionGap", "reasonCode", value.ReasonCode, "offendingSubject", value.OffendingSubject, "projectorEpoch", value.ProjectorEpoch, "declarationContentDigest", value.DeclarationContentDigest);

    private static ProjectionGap? ReadNullableGap(JsonElement parent, string name)
    {
        var element = parent.GetProperty(name);
        if (element.ValueKind == JsonValueKind.Null) return null;
        var obj = Typed(element, "ProjectionGap", "reasonCode", "offendingSubject", "projectorEpoch", "declarationContentDigest");
        return new ProjectionGap(ReadString(obj, "reasonCode"), ReadString(obj, "offendingSubject"), ReadString(obj, "projectorEpoch"), ReadString(obj, "declarationContentDigest"));
    }

    private static ProjectionGap? ReadNullableGap(JsonObject parent, string name) => ReadNullableGap(Element(parent), name);

    private static JsonObject WriteProvenance(AssessedProvenance value) => value switch
    {
        AssessedProvenance.RepoDerived repo => Obj("type", "RepoDerived", "acknowledgements", WriteStrings(repo.Acknowledgements.Select(static item => item.Value))),
        AssessedProvenance.LiteratureAttested literature => Obj("type", "LiteratureAttested", "noteRef", literature.NoteRef.Value),
        AssessedProvenance.SuspectedNovel novel => Obj("type", "SuspectedNovel", "searchReceipt", novel.SearchReceipt.Value, "acknowledgements", WriteStrings(novel.Acknowledgements.Select(static item => item.Value))),
        _ => throw Unknown(value),
    };

    private static AssessedProvenance ReadProvenance(JsonElement parent, string name)
    {
        var obj = RequireObject(parent.GetProperty(name));
        return ReadType(obj) switch
        {
            "RepoDerived" => ReadTyped(obj, "RepoDerived", "acknowledgements", () => AssessedProvenance.FromRepo(ReadStrings(obj, "acknowledgements").Select(LibraryNoteRef.Create).ToArray())),
            "LiteratureAttested" => ReadTyped(obj, "LiteratureAttested", "noteRef", () => AssessedProvenance.FromLiterature(LibraryNoteRef.Create(ReadString(obj, "noteRef")))),
            "SuspectedNovel" => ReadTyped(obj, "SuspectedNovel", "searchReceipt", "acknowledgements", () => AssessedProvenance.NovelAfterSearch(GidRef.Create(ReadString(obj, "searchReceipt")), ReadStrings(obj, "acknowledgements").Select(LibraryNoteRef.Create).ToArray())),
            _ => throw UnknownType(obj),
        };
    }

    private static AssessedProvenance ReadProvenance(JsonObject parent, string name) => ReadProvenance(Element(parent), name);

    private static JsonObject WriteClaim(OpenProblemResolutionClaim value) => Obj("type", "OpenProblemResolutionClaim", "problemSlug", value.ProblemSlug.Value, "resolutionKind", value.ResolutionKind.ToString(), "additionalMembers", WriteStrings(value.AdditionalMembers));

    private static OpenProblemResolutionClaim? ReadNullableClaim(JsonElement parent, string name)
    {
        var element = parent.GetProperty(name);
        if (element.ValueKind == JsonValueKind.Null) return null;
        var obj = Typed(element, "OpenProblemResolutionClaim", "problemSlug", "resolutionKind", "additionalMembers");
        return new OpenProblemResolutionClaim(ProblemSlugRef.Create(ReadString(obj, "problemSlug")), ParseEnum<ResolutionKind>(obj, "resolutionKind"), ReadStrings(obj, "additionalMembers").Select(DeclarationHandle.Create));
    }

    private static OpenProblemResolutionClaim? ReadNullableClaim(JsonObject parent, string name) => ReadNullableClaim(Element(parent), name);

    private static JsonObject WriteEdge(DocumentEdge value) => value switch
    {
        DocumentEdge.TruthAnchor anchor => Obj("type", "TruthAnchor", "target", anchor.Target.Value, "describeId", anchor.DescribeId?.Value),
        DocumentEdge.Dependency dependency => Obj("type", "Dependency", "target", dependency.Target.Value),
        DocumentEdge.NarrativeReference narrative => Obj("type", "NarrativeReference", "target", WriteNarrativeTarget(narrative.Target)),
        _ => throw Unknown(value),
    };

    private static DocumentEdge ReadEdge(JsonElement value)
    {
        var obj = RequireObject(value);
        return ReadType(obj) switch
        {
            "TruthAnchor" => ReadTyped(obj, "TruthAnchor", "target", "describeId", () => ReadNullableString(obj, "describeId") is { } id ? DocumentEdge.TruthAnchor.FromDescribe(LeanDeclarationRef.Create(ReadString(obj, "target")), DescribeId.Create(id)) : DocumentEdge.TruthAnchor.Create(LeanDeclarationRef.Create(ReadString(obj, "target")))),
            "Dependency" => ReadTyped(obj, "Dependency", "target", () => DocumentEdge.Dependency.Create(GidRef.Create(ReadString(obj, "target")))),
            "NarrativeReference" => ReadTyped(obj, "NarrativeReference", "target", () => ReadNarrativeReference(obj, "target")),
            _ => throw UnknownType(obj),
        };
    }

    private static JsonObject WriteNarrativeTarget(NarrativeTarget value) => value switch
    {
        NarrativeTarget.Document document => Obj("type", "Document", "documentGid", document.DocumentGid.Value),
        NarrativeTarget.Describe describe => Obj("type", "Describe", "documentGid", describe.DocumentGid.Value, "describeId", describe.DescribeId.Value),
        _ => throw Unknown(value),
    };

    private static DocumentEdge ReadNarrativeReference(JsonElement parent, string name)
    {
        var obj = RequireObject(parent.GetProperty(name));
        return ReadType(obj) switch
        {
            "Document" => ReadTyped(obj, "Document", "documentGid", () => DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(ReadString(obj, "documentGid")))),
            "Describe" => ReadTyped(obj, "Describe", "documentGid", "describeId", () => DocumentEdge.NarrativeReference.ToDescribe(GidRef.Create(ReadString(obj, "documentGid")), DescribeId.Create(ReadString(obj, "describeId")))),
            _ => throw UnknownType(obj),
        };
    }

    private static DocumentEdge ReadNarrativeReference(JsonObject parent, string name) => ReadNarrativeReference(Element(parent), name);

    private static JsonNode WriteFormula(Formula value) => value switch
    {
        Formula.Aligned aligned => Obj("type", "Aligned", "rows", new JsonArray(aligned.Rows.Select(WriteFormula).ToArray())),
        Formula.LatexSequence sequence => Obj("type", "LatexSequence", "items", new JsonArray(sequence.Items.Select(WriteFormula).ToArray())),
        Formula.LatexGroup group => Obj("type", "LatexGroup", "items", new JsonArray(group.Items.Select(WriteFormula).ToArray())),
        Formula.LatexMacro macro => Obj("type", "LatexMacro", "value", macro.Value.ToString()),
        Formula.LatexSymbol symbol => Obj("type", "LatexSymbol", "value", symbol.Value.ToString()),
        Formula.LatexSpace => Obj("type", "LatexSpace"),
        Formula.LatexNewline => Obj("type", "LatexNewline"),
        Formula.LatexWord word => Obj("type", "LatexWord", "value", word.Value.Value),
        Formula.LatexDigits digits => Obj("type", "LatexDigits", "digits", new JsonArray(digits.Digits.Select(static item => JsonValue.Create((int)item)).ToArray())),
        Formula.Layout layout => Obj("type", "Layout", "mode", layout.Mode.ToString(), "content", WriteFormula(layout.Content)),
        Formula.Symbol symbol => Obj("type", "Symbol", "name", symbol.Name.Value),
        Formula.Number number => Obj("type", "Number", "value", number.Value),
        Formula.Phi => Obj("type", "Phi"),
        Formula.Psi => Obj("type", "Psi"),
        Formula.Placeholder => Obj("type", "Placeholder"),
        Formula.Integers => Obj("type", "Integers"),
        Formula.NamedConstant constant => Obj("type", "NamedConstant", "name", constant.Name.Value),
        Formula.Negate negate => Obj("type", "Negate", "operand", WriteFormula(negate.Operand)),
        Formula.Absolute absolute => Obj("type", "Absolute", "operand", WriteFormula(absolute.Operand)),
        Formula.Norm norm => Obj("type", "Norm", "operand", WriteFormula(norm.Operand)),
        Formula.Binary binary => Obj("type", "Binary", "left", WriteFormula(binary.Left), "operator", binary.Operator.ToString(), "right", WriteFormula(binary.Right)),
        Formula.Fraction fraction => Obj("type", "Fraction", "numerator", WriteFormula(fraction.Numerator), "denominator", WriteFormula(fraction.Denominator)),
        Formula.Subscript subscript => Obj("type", "Subscript", "base", WriteFormula(subscript.Base), "index", WriteFormula(subscript.Index)),
        Formula.Power power => Obj("type", "Power", "base", WriteFormula(power.Base), "exponent", WriteFormula(power.Exponent)),
        Formula.Floor floor => Obj("type", "Floor", "operand", WriteFormula(floor.Operand)),
        Formula.Log log => Obj("type", "Log", "base", WriteFormula(log.Base), "argument", WriteFormula(log.Argument)),
        Formula.Modulo modulo => Obj("type", "Modulo", "value", WriteFormula(modulo.Value), "modulus", WriteFormula(modulo.Modulus)),
        Formula.Sequence sequence => Obj("type", "Sequence", "element", WriteFormula(sequence.Element), "index", WriteFormula(sequence.Index), "domain", WriteFormula(sequence.Domain)),
        Formula.SetLiteral set => Obj("type", "SetLiteral", "elements", new JsonArray(set.Elements.Select(WriteFormula).ToArray())),
        Formula.SetBuilder builder => Obj("type", "SetBuilder", "element", WriteFormula(builder.Element), "variable", WriteFormula(builder.Variable), "domain", WriteFormula(builder.Domain)),
        Formula.FunctionCall call => Obj("type", "FunctionCall", "name", call.Name.Value, "arguments", new JsonArray(call.Arguments.Select(WriteFormula).ToArray())),
        Formula.Apply apply => Obj("type", "Apply", "function", WriteFormula(apply.Function), "arguments", new JsonArray(apply.Arguments.Select(WriteFormula).ToArray())),
        Formula.TypeArrow arrow => Obj("type", "TypeArrow", "domain", WriteFormula(arrow.Domain), "codomain", WriteFormula(arrow.Codomain)),
        Formula.Relation relation => Obj("type", "Relation", "left", WriteFormula(relation.Left), "operator", relation.Operator.ToString(), "right", WriteFormula(relation.Right)),
        Formula.RelationChain chain => Obj("type", "RelationChain", "operator", chain.Operator.ToString(), "operands", new JsonArray(chain.Operands.Select(WriteFormula).ToArray())),
        Formula.Logic logic => Obj("type", "Logic", "left", WriteFormula(logic.Left), "operator", logic.Operator.ToString(), "right", WriteFormula(logic.Right)),
        Formula.Not not => Obj("type", "Not", "operand", WriteFormula(not.Operand)),
        Formula.Bind bind => Obj("type", "Bind", "quantifier", bind.Quantifier.ToString(), "variable", bind.Variable.Value, "domain", WriteFormula(bind.Domain), "body", WriteFormula(bind.Body)),
        Formula.BindMany many => Obj("type", "BindMany", "quantifier", many.Quantifier.ToString(), "variables", new JsonArray(many.Variables.Select(WriteBoundVariable).ToArray()), "body", WriteFormula(many.Body)),
        _ => throw Unknown(value),
    };

    private static JsonObject WriteBoundVariable(Formula.BoundVariable value) => Obj("type", "BoundVariable", "name", value.Name.Value, "domain", WriteFormula(value.Domain));

    private static Formula ReadFormula(JsonElement parent, string name) => ReadFormula(parent.GetProperty(name));

    private static Formula ReadFormula(JsonObject parent, string name) => ReadFormula(Element(parent), name);

    private static Formula ReadFormula(JsonElement value)
    {
        var obj = RequireObject(value);
        return ReadType(obj) switch
        {
            "Aligned" => ReadTyped(obj, "Aligned", "rows", () => new Formula.Aligned(ReadArray(obj, "rows").EnumerateArray().Select(ReadFormula).ToImmutableArray())),
            "LatexSequence" => ReadTyped(obj, "LatexSequence", "items", () => new Formula.LatexSequence(ReadArray(obj, "items").EnumerateArray().Select(ReadFormula).ToImmutableArray())),
            "LatexGroup" => ReadTyped(obj, "LatexGroup", "items", () => new Formula.LatexGroup(ReadArray(obj, "items").EnumerateArray().Select(ReadFormula).ToImmutableArray())),
            "LatexMacro" => ReadTyped(obj, "LatexMacro", "value", () => new Formula.LatexMacro(ParseEnum<FormulaLatexMacro>(obj, "value"))),
            "LatexSymbol" => ReadTyped(obj, "LatexSymbol", "value", () => new Formula.LatexSymbol(ParseEnum<FormulaLatexSymbol>(obj, "value"))),
            "LatexSpace" => ReadTyped(obj, "LatexSpace" , () => new Formula.LatexSpace()),
            "LatexNewline" => ReadTyped(obj, "LatexNewline", () => new Formula.LatexNewline()),
            "LatexWord" => ReadTyped(obj, "LatexWord", "value", () => new Formula.LatexWord(FormulaIdentifier.Create(ReadString(obj, "value")))),
            "LatexDigits" => ReadTyped(obj, "LatexDigits", "digits", () => new Formula.LatexDigits(ReadArray(obj, "digits").EnumerateArray().Select(ReadByte).ToImmutableArray())),
            "Layout" => ReadTyped(obj, "Layout", "mode", "content", () => new Formula.Layout(ParseEnum<FormulaLayoutMode>(obj, "mode"), ReadFormula(obj, "content"))),
            "Symbol" => ReadTyped(obj, "Symbol", "name", () => new Formula.Symbol(FormulaIdentifier.Create(ReadString(obj, "name")))),
            "Number" => ReadTyped(obj, "Number", "value", () => new Formula.Number(ReadLong(obj, "value"))),
            "Phi" => ReadTyped(obj, "Phi", () => new Formula.Phi()),
            "Psi" => ReadTyped(obj, "Psi", () => new Formula.Psi()),
            "Placeholder" => ReadTyped(obj, "Placeholder", () => new Formula.Placeholder()),
            "Integers" => ReadTyped(obj, "Integers", () => new Formula.Integers()),
            "NamedConstant" => ReadTyped(obj, "NamedConstant", "name", () => new Formula.NamedConstant(FormulaIdentifier.Create(ReadString(obj, "name")))),
            "Negate" => ReadTyped(obj, "Negate", "operand", () => new Formula.Negate(ReadFormula(obj, "operand"))),
            "Absolute" => ReadTyped(obj, "Absolute", "operand", () => new Formula.Absolute(ReadFormula(obj, "operand"))),
            "Norm" => ReadTyped(obj, "Norm", "operand", () => new Formula.Norm(ReadFormula(obj, "operand"))),
            "Binary" => ReadTyped(obj, "Binary", "left", "operator", "right", () => new Formula.Binary(ReadFormula(obj, "left"), ParseEnum<FormulaBinaryOperator>(obj, "operator"), ReadFormula(obj, "right"))),
            "Fraction" => ReadTyped(obj, "Fraction", "numerator", "denominator", () => new Formula.Fraction(ReadFormula(obj, "numerator"), ReadFormula(obj, "denominator"))),
            "Subscript" => ReadTyped(obj, "Subscript", "base", "index", () => new Formula.Subscript(ReadFormula(obj, "base"), ReadFormula(obj, "index"))),
            "Power" => ReadTyped(obj, "Power", "base", "exponent", () => new Formula.Power(ReadFormula(obj, "base"), ReadFormula(obj, "exponent"))),
            "Floor" => ReadTyped(obj, "Floor", "operand", () => new Formula.Floor(ReadFormula(obj, "operand"))),
            "Log" => ReadTyped(obj, "Log", "base", "argument", () => new Formula.Log(ReadFormula(obj, "base"), ReadFormula(obj, "argument"))),
            "Modulo" => ReadTyped(obj, "Modulo", "value", "modulus", () => new Formula.Modulo(ReadFormula(obj, "value"), ReadFormula(obj, "modulus"))),
            "Sequence" => ReadTyped(obj, "Sequence", "element", "index", "domain", () => new Formula.Sequence(ReadFormula(obj, "element"), ReadFormula(obj, "index"), ReadFormula(obj, "domain"))),
            "SetLiteral" => ReadTyped(obj, "SetLiteral", "elements", () => new Formula.SetLiteral(ReadArray(obj, "elements").EnumerateArray().Select(ReadFormula).ToImmutableArray())),
            "SetBuilder" => ReadTyped(obj, "SetBuilder", "element", "variable", "domain", () => new Formula.SetBuilder(ReadFormula(obj, "element"), ReadFormula(obj, "variable"), ReadFormula(obj, "domain"))),
            "FunctionCall" => ReadTyped(obj, "FunctionCall", "name", "arguments", () => new Formula.FunctionCall(FormulaIdentifier.Create(ReadString(obj, "name")), ReadArray(obj, "arguments").EnumerateArray().Select(ReadFormula).ToImmutableArray())),
            "Apply" => ReadTyped(obj, "Apply", "function", "arguments", () => new Formula.Apply(ReadFormula(obj, "function"), ReadArray(obj, "arguments").EnumerateArray().Select(ReadFormula).ToImmutableArray())),
            "TypeArrow" => ReadTyped(obj, "TypeArrow", "domain", "codomain", () => new Formula.TypeArrow(ReadFormula(obj, "domain"), ReadFormula(obj, "codomain"))),
            "Relation" => ReadTyped(obj, "Relation", "left", "operator", "right", () => new Formula.Relation(ReadFormula(obj, "left"), ParseEnum<FormulaRelationOperator>(obj, "operator"), ReadFormula(obj, "right"))),
            "RelationChain" => ReadTyped(obj, "RelationChain", "operator", "operands", () => new Formula.RelationChain(ParseEnum<FormulaRelationOperator>(obj, "operator"), ReadArray(obj, "operands").EnumerateArray().Select(ReadFormula).ToImmutableArray())),
            "Logic" => ReadTyped(obj, "Logic", "left", "operator", "right", () => new Formula.Logic(ReadFormula(obj, "left"), ParseEnum<FormulaLogicOperator>(obj, "operator"), ReadFormula(obj, "right"))),
            "Not" => ReadTyped(obj, "Not", "operand", () => new Formula.Not(ReadFormula(obj, "operand"))),
            "Bind" => ReadTyped(obj, "Bind", "quantifier", "variable", "domain", "body", () => new Formula.Bind(ParseEnum<FormulaQuantifier>(obj, "quantifier"), FormulaIdentifier.Create(ReadString(obj, "variable")), ReadFormula(obj, "domain"), ReadFormula(obj, "body"))),
            "BindMany" => ReadTyped(obj, "BindMany", "quantifier", "variables", "body", () => new Formula.BindMany(ParseEnum<FormulaQuantifier>(obj, "quantifier"), ReadArray(obj, "variables").EnumerateArray().Select(ReadBoundVariable).ToImmutableArray(), ReadFormula(obj, "body"))),
            _ => throw UnknownType(obj),
        };
    }

    private static Formula.BoundVariable ReadBoundVariable(JsonElement value)
    {
        var obj = Typed(value, "BoundVariable", "name", "domain");
        return new Formula.BoundVariable(FormulaIdentifier.Create(ReadString(obj, "name")), ReadFormula(obj, "domain"));
    }

    private static JsonArray WriteStrings(IEnumerable<string> values) =>
        new(values.Select(static value => JsonValue.Create(value)).ToArray());

    private static IEnumerable<string> ReadStrings(JsonElement parent, string name) =>
        ReadArray(parent, name).EnumerateArray().Select(item => ReadRequiredString(item, name));

    private static IEnumerable<string> ReadStrings(JsonObject parent, string name) => ReadStrings(Element(parent), name);

    private static Formula? ReadNullableFormula(JsonElement parent, string name)
    {
        var value = parent.GetProperty(name);
        return value.ValueKind == JsonValueKind.Null ? null : ReadFormula(value);
    }

    private static Formula? ReadNullableFormula(JsonObject parent, string name) => ReadNullableFormula(Element(parent), name);

    private static JsonObject Obj(string firstName, object? firstValue, params object?[] rest)
    {
        var result = new JsonObject { [firstName] = ToNode(firstValue) };
        if (rest.Length % 2 != 0) throw new InvalidOperationException("JSON object fields must be pairs.");
        for (var index = 0; index < rest.Length; index += 2)
        {
            result[(string)rest[index]!] = ToNode(rest[index + 1]);
        }
        return result;
    }

    private static JsonNode? ToNode(object? value) => value switch
    {
        null => null,
        JsonNode node => node,
        _ => JsonValue.Create(value),
    };

    private static JsonObject RequireObject(JsonElement value) => value.ValueKind is JsonValueKind.Object
        ? value.Deserialize<JsonObject>(JsonOptions) ?? throw Invalid("Object is null.")
        : throw InvalidType("Expected an object.");

    private static JsonElement Element(JsonObject value)
    {
        using var document = JsonDocument.Parse(value.ToJsonString(JsonOptions), JsonParseOptions);
        return document.RootElement.Clone();
    }

    private static JsonObject Typed(JsonElement value, string type, params string[] fields)
    {
        var obj = RequireObject(value);
        return Typed(obj, type, fields);
    }

    private static JsonObject Typed(JsonObject obj, string type, params string[] fields)
    {
        if (!string.Equals(ReadType(obj), type, StringComparison.Ordinal)) throw UnknownType(obj);
        using var document = JsonDocument.Parse(obj.ToJsonString(JsonOptions), JsonParseOptions);
        var element = document.RootElement;
        RequireFields(element, new[] { "type" }.Concat(fields).ToArray());
        return obj;
    }

    private static T ReadTyped<T>(JsonObject obj, string type, Func<T> reader, params string[] fields)
    {
        Typed(obj, type, fields);
        return ReadValue(reader);
    }

    private static T ReadTyped<T>(JsonObject obj, string type, string field, Func<T> reader) =>
        ReadTyped(obj, type, reader, field);

    private static T ReadTyped<T>(JsonObject obj, string type, string field1, string field2, Func<T> reader) =>
        ReadTyped(obj, type, reader, field1, field2);

    private static T ReadTyped<T>(JsonObject obj, string type, string field1, string field2, string field3, Func<T> reader) =>
        ReadTyped(obj, type, reader, field1, field2, field3);

    private static T ReadTyped<T>(JsonObject obj, string type, string field1, string field2, string field3, string field4, Func<T> reader) =>
        ReadTyped(obj, type, reader, field1, field2, field3, field4);

    private static T ReadValue<T>(Func<T> reader)
    {
        try { return reader(); }
        catch (ScribeResourceException) { throw; }
        catch (Exception exception) when (exception is ArgumentException or InvalidOperationException or FormatException or JsonException)
        {
            throw new ScribeResourceException(ScribeResourceErrorCode.InvalidValue, exception.Message, exception);
        }
    }

    private static void RequireFields(JsonElement value, params string[] fields)
    {
        if (value.ValueKind is not JsonValueKind.Object)
        {
            throw InvalidType("Expected an object.");
        }

        var expected = fields.ToHashSet(StringComparer.Ordinal);
        foreach (var property in value.EnumerateObject())
        {
            if (!expected.Contains(property.Name))
            {
                throw new ScribeResourceException(ScribeResourceErrorCode.ExtraField, $"Unexpected field '{property.Name}'.");
            }
        }

        foreach (var field in fields)
        {
            if (!value.TryGetProperty(field, out _))
            {
                throw new ScribeResourceException(ScribeResourceErrorCode.MissingField, $"Missing field '{field}'.");
            }
        }
    }

    private static string ReadType(JsonObject value)
    {
        if (value["type"] is null)
        {
            throw new ScribeResourceException(ScribeResourceErrorCode.MissingField, "Missing field 'type'.");
        }

        return value["type"] is JsonValue type
            && type.TryGetValue<string>(out var result)
                ? result
                : throw InvalidType("Field 'type' must be a string.");
    }

    private static string ReadString(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) ? ReadRequiredString(value, name) : throw Missing(name);

    private static string ReadString(JsonObject parent, string name) =>
        parent[name] is JsonValue value && value.TryGetValue<string>(out var result) ? result : throw Missing(name);

    private static string ReadRequiredString(JsonElement value, string name) => value.ValueKind is JsonValueKind.String
        ? value.GetString() ?? throw Invalid($"Field '{name}' is null.")
        : throw InvalidType($"Field '{name}' must be a string.");

    private static string? ReadNullableString(JsonObject parent, string name)
    {
        if (parent[name] is null) return null;
        if (parent[name] is JsonValue value && value.GetValueKind() is JsonValueKind.Null) return null;
        return parent[name] is JsonValue text && text.TryGetValue<string>(out var result)
            ? result
            : throw InvalidType($"Field '{name}' must be a string or null.");
    }

    private static int ReadInt(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind is JsonValueKind.Number && value.TryGetInt32(out var result)
            ? result : throw InvalidType($"Field '{name}' must be an integer.");

    private static long ReadLong(JsonObject parent, string name) =>
        parent[name] is JsonValue value && value.TryGetValue<long>(out var result)
            ? result : throw InvalidType($"Field '{name}' must be an integer.");

    private static byte ReadByte(JsonElement value) =>
        value.ValueKind is JsonValueKind.Number && value.TryGetByte(out var result)
            ? result : throw InvalidType("Array item must be a byte.");

    private static JsonElement ReadArray(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind is JsonValueKind.Array
            ? value : throw InvalidType($"Field '{name}' must be an array.");

    private static JsonElement ReadArray(JsonObject parent, string name) =>
        parent[name] is JsonArray ? Element(parent).GetProperty(name) : throw InvalidType($"Field '{name}' must be an array.");

    private static T ParseEnum<T>(JsonObject parent, string name) where T : struct, Enum
    {
        var value = parent[name]?.GetValue<string>() ?? throw InvalidType($"Field '{name}' must be a string.");
        return Enum.TryParse<T>(value, false, out var parsed) && Enum.IsDefined(parsed)
            ? parsed : throw new ScribeResourceException(ScribeResourceErrorCode.InvalidValue, $"Unknown {typeof(T).Name} value '{value}'.");
    }

    private static T? ReadNullableEnum<T>(JsonObject parent, string name) where T : struct, Enum
    {
        var value = parent[name];
        if (value is null || value.GetValueKind() is JsonValueKind.Null) return null;
        return ParseEnum<T>(parent, name);
    }

    private static ScribeResourceException Missing(string name) => new(ScribeResourceErrorCode.MissingField, $"Missing field '{name}'.");
    private static ScribeResourceException Invalid(string message) => new(ScribeResourceErrorCode.InvalidValue, message);
    private static ScribeResourceException InvalidType(string message) => new(ScribeResourceErrorCode.TypeMismatch, message);
    private static ScribeResourceException UnknownType(JsonObject value) => new(ScribeResourceErrorCode.UnknownType, $"Unknown type '{ReadType(value)}'.");
    private static ScribeResourceException Unknown(object value) => new(ScribeResourceErrorCode.UnknownType, $"Unsupported AST type '{value.GetType().FullName}'.");
}
