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
        var restored = claim is null ? DocumentBlock.Describe.Restore(
            DescribeId.Create(ReadString(obj, "id")),
            Heading.Create(ReadString(obj, "title")),
            statement,
            ReadProvenance(obj, "provenance"),
            ReadBlocks(obj, "content"),
            statementFormula,
            statementSource,
            kindSource) : RestoreClaimDescribe(obj, statement, kindSource, statementFormula, statementSource, claim);
        if (restored.FormulaProvenance != expectedProvenance)
        {
            throw new ScribeResourceException(
                ScribeResourceErrorCode.InvalidValue,
                "Statement formula provenance does not match the decoded statement source.");
        }

        return restored;
    }

    private static DocumentBlock.Describe ReadDescribe(JsonObject value) => ReadDescribe(Element(value));

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
