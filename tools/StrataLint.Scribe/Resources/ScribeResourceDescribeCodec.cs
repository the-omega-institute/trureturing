using System.Text.Json;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe;

public static partial class ScribeResourceCodec
{
    private static DocumentBlock.Describe ReadDescribe(JsonElement value)
    {
        var obj = Typed(value, "Describe", "id", "title", "statement", "kindSource", "provenance", "content", "statementFormula", "statementFormulaProvenance", "statementSource", "claim");
        var statement = ReadStatement(obj, "statement");
        var kindSource = ReadKindSource(obj, "kindSource");
        var statementFormula = ReadNullableFormula(obj, "statementFormula");
        var statementSource = ReadNullableStatementSource(obj, "statementSource");
        var expectedProvenance = ParseEnum<StatementFormulaProvenance>(obj, "statementFormulaProvenance");
        if (expectedProvenance == StatementFormulaProvenance.LeanDerived
            && statementSource is null)
        {
            if (statementFormula is null || statement is not DescribeStatement.LeanDeclaration lean)
            {
                throw new ScribeResourceException(
                    ScribeResourceErrorCode.InvalidValue,
                    "Lean-derived formula provenance requires a Lean declaration and formula.");
            }

            StatementProjectionFixtureLoader.RestoreDerived(statementFormula, lean.Value);
        }

        var claim = ReadNullableClaim(obj, "claim");
        var restored = claim is null
            ? RestoreDescribe(obj, statement, kindSource, statementFormula, statementSource)
            : RestoreClaimDescribe(obj, statement, kindSource, statementFormula, statementSource, claim);
        if (restored.FormulaProvenance != expectedProvenance)
        {
            throw new ScribeResourceException(
                ScribeResourceErrorCode.InvalidValue,
                "Statement formula provenance does not match the decoded statement source.");
        }

        return restored;
    }

    private static DocumentBlock.Describe ReadDescribe(JsonObject value) => ReadDescribe(Element(value));

    private static DocumentBlock.Describe RestoreDescribe(
        JsonObject obj,
        DescribeStatement statement,
        DescribeKindSource kindSource,
        Formula? formula,
        StatementSource? source)
    {
        var id = DescribeId.Create(ReadString(obj, "id"));
        var title = Heading.Create(ReadString(obj, "title"));
        var provenance = ReadProvenance(obj, "provenance");
        var content = ReadBlocks(obj, "content");

        if (statement is DescribeStatement.FormulaAst authored)
        {
            if (kindSource is not DescribeKindSource.Authored authoredKind
                || authoredKind.Value is not (DescribeKind.Remark or DescribeKind.Example)
                || formula is not null
                || source is not null)
            {
                throw InvalidDescribe("An authored formula requires an authored remark or example kind and no statement source.");
            }

            return authoredKind.Value == DescribeKind.Example
                ? DocumentBlock.Describe.AuthoredFormula(id, DescribeKind.Example, title, authored.Value, provenance, content)
                : DocumentBlock.Describe.AuthoredFormula(id, DescribeKind.Remark, title, authored.Value, provenance, content);
        }

        var lean = (DescribeStatement.LeanDeclaration)statement;
        if (kindSource is DescribeKindSource.Authored
            && source is null
            && formula is not null
            && StatementProjectionFixtureLoader.IsDerivedFrom(formula, lean.Value))
        {
            return DocumentBlock.Describe.Restore(
                id, title, statement, provenance, content, formula, source, kindSource);
        }

        if (kindSource is not DescribeKindSource.ReportDerived derived
            || !string.Equals(lean.Value.Value, derived.Handle.Value, StringComparison.Ordinal))
        {
            throw InvalidDescribe("A Lean declaration requires a matching report-derived handle.");
        }

        if (derived.Role == DescribeRole.Remark)
        {
            if (formula is not null || source is not null)
            {
                throw InvalidDescribe("A declaration remark cannot carry a statement source or formula.");
            }

            return DocumentBlock.Describe.RemarkOn(id, derived.Handle, title, provenance, content);
        }

        if (source is null)
        {
            throw InvalidDescribe("A report-derived declaration requires a statement source.");
        }

        if (source is StatementSource.NoFormula && formula is not null
            || source is StatementSource.Authored && formula is null
            || source is StatementSource.LeanDerived && formula is null)
        {
            throw InvalidDescribe("Statement source and materialized formula do not match.");
        }

        return DocumentBlock.Describe.ReportDerived(
            id,
            title,
            derived.Handle,
            source,
            provenance,
            content,
            derived.Role,
            openProblemResolutionClaim: null,
            restoredStatement: (source, formula));
    }

    private static ScribeResourceException InvalidDescribe(string message) =>
        new(ScribeResourceErrorCode.InvalidValue, message);

    private static DocumentBlock.Describe RestoreClaimDescribe(
        JsonObject obj,
        DescribeStatement statement,
        DescribeKindSource kindSource,
        Formula? formula,
        StatementSource? source,
        OpenProblemResolutionClaim claim)
    {
        if (statement is not DescribeStatement.LeanDeclaration lean
            || kindSource is not DescribeKindSource.ReportDerived derived
            || derived.Role == DescribeRole.Remark
            || !string.Equals(lean.Value.Value, derived.Handle.Value, StringComparison.Ordinal)
            || source is null)
        {
            throw new ScribeResourceException(ScribeResourceErrorCode.InvalidValue,
                "A resolution claim requires its matching report-derived Lean declaration and statement source.");
        }

        return DocumentBlock.Describe.ReportDerived(
            DescribeId.Create(ReadString(obj, "id")),
            Heading.Create(ReadString(obj, "title")),
            derived.Handle,
            source,
            ReadProvenance(obj, "provenance"),
            ReadBlocks(obj, "content"),
            derived.Role,
            claim,
            restoredStatement: (source, formula));
    }
}
