using System.Globalization;
using System.Text;

namespace StrataLint.Cli;

internal static class TomlGoldenWriter
{
    internal const string OntologyHeader =
        "# 输入=spec 场景采样(人);期望=Engine 输出快照(机器录制);此文件是行为时间锁\n";
    internal const string CanonicalHeader =
        "# canonical: UTF-8 without BOM; LF; case keys=name,changes,baseline_mutations,mutations,expected_diagnostics; nested keys follow schema order.\n";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static byte[] Write(IReadOnlyList<GoldenCase> cases)
    {
        ArgumentNullException.ThrowIfNull(cases);
        if (cases.Count == 0)
        {
            throw new ArgumentException("golden TOML file must contain at least one case", nameof(cases));
        }

        var builder = new StringBuilder(OntologyHeader).Append(CanonicalHeader);
        for (var index = 0; index < cases.Count; index++)
        {
            if (index > 0) builder.Append('\n');
            WriteCase(builder, cases[index]);
        }

        return StrictUtf8.GetBytes(builder.ToString());
    }

    private static void WriteCase(StringBuilder builder, GoldenCase testCase)
    {
        builder.Append("[[cases]]\nname = ");
        WriteString(builder, testCase.Name);
        builder.Append("\nchanges = ");
        WriteStringArray(builder, testCase.Changes);
        builder.Append("\nbaseline_mutations = ");
        WriteMutationArray(builder, testCase.BaselineMutations);
        builder.Append("\nmutations = ");
        WriteMutationArray(builder, testCase.Mutations);
        builder.Append("\nexpected_diagnostics = ");
        WriteDiagnosticArray(builder, testCase.ExpectedDiagnostics);
        builder.Append('\n');
    }

    private static void WriteStringArray(StringBuilder builder, IReadOnlyList<string> values)
    {
        builder.Append('[');
        for (var index = 0; index < values.Count; index++)
        {
            if (index > 0) builder.Append(", ");
            WriteString(builder, values[index]);
        }

        builder.Append(']');
    }

    private static void WriteMutationArray(
        StringBuilder builder,
        IReadOnlyList<GoldenMutation> mutations)
    {
        builder.Append('[');
        for (var index = 0; index < mutations.Count; index++)
        {
            if (index > 0) builder.Append(", ");
            WriteMutation(builder, mutations[index]);
        }

        builder.Append(']');
    }

    private static void WriteMutation(StringBuilder builder, GoldenMutation mutation)
    {
        builder.Append("{ op = ");
        switch (mutation)
        {
            case GoldenMutation.Write write:
                WriteString(builder, "write");
                WriteField(builder, "path", write.Path);
                WriteField(builder, "content", write.Content);
                break;
            case GoldenMutation.WriteParts write:
                WriteString(builder, "write_parts");
                WriteField(builder, "path", write.Path);
                builder.Append(", parts = ");
                WriteStringArray(builder, write.Parts);
                break;
            case GoldenMutation.Lean lean:
                WriteString(builder, "lean");
                WriteField(builder, "path", lean.Path);
                WriteField(builder, "raw_gid", lean.RawGid);
                WriteField(builder, "generality", lean.Generality.ToString());
                WriteField(builder, "body", lean.Body);
                break;
            case GoldenMutation.Delete delete:
                WriteString(builder, "delete");
                WriteField(builder, "path", delete.Path);
                break;
            case GoldenMutation.AppendLines append:
                WriteString(builder, "append_lines");
                WriteField(builder, "path", append.Path);
                builder.Append(", count = ").Append(append.Count);
                WriteField(builder, "line", append.Line);
                break;
            case GoldenMutation.AddDomain domain:
                WriteString(builder, "add_domain");
                WriteField(builder, "name", domain.Name);
                WriteField(builder, "stratum", domain.Stratum.ToString());
                break;
            case GoldenMutation.AddTask task:
                WriteString(builder, "add_task");
                WriteField(builder, "path", task.Path);
                WriteField(builder, "raw_gid", task.RawGid);
                WriteField(builder, "raw_case_id", task.RawCaseId);
                break;
            case GoldenMutation.PopulateDirectory:
                WriteString(builder, "populate_directory");
                break;
            case GoldenMutation.EmptyMirrorWaiver:
                WriteString(builder, "empty_mirror_waiver");
                break;
            case GoldenMutation.EvidenceMirror mirror:
                WriteString(builder, "evidence_mirror");
                WriteBooleanField(builder, "include_json", mirror.IncludeJson);
                WriteBooleanField(builder, "include_yaml", mirror.IncludeYaml);
                break;
            case GoldenMutation.ReplaceBackfill replace:
                WriteString(builder, "replace_backfill");
                WriteField(builder, "old_value", replace.OldValue);
                WriteField(builder, "new_value", replace.NewValue);
                break;
            case GoldenMutation.ReplaceFirstBackfillDisposition disposition:
                WriteString(builder, "replace_first_backfill_disposition");
                WriteField(builder, "raw_gid", disposition.RawGid);
                break;
            case GoldenMutation.MutateBackfillAnchor anchor:
                WriteString(builder, "mutate_backfill_anchor");
                WriteField(builder, "anchor", anchor.Anchor);
                WriteBooleanField(builder, "duplicate", anchor.Duplicate);
                break;
            default:
                throw new InvalidOperationException(
                    $"unsupported golden mutation: {mutation.GetType().Name}");
        }

        builder.Append(" }");
    }

    private static void WriteDiagnosticArray(
        StringBuilder builder,
        IReadOnlyList<GoldenDiagnostic> diagnostics)
    {
        builder.Append('[');
        for (var index = 0; index < diagnostics.Count; index++)
        {
            if (index > 0) builder.Append(", ");
            var diagnostic = diagnostics[index];
            builder.Append("{ rule = ").Append(diagnostic.RuleNumber).Append(", path = ");
            WriteString(builder, diagnostic.Path);
            builder.Append(", message = ");
            WriteString(builder, diagnostic.Message);
            builder.Append(" }");
        }

        builder.Append(']');
    }

    private static void WriteField(StringBuilder builder, string name, string value)
    {
        builder.Append(", ").Append(name).Append(" = ");
        WriteString(builder, value);
    }

    private static void WriteBooleanField(StringBuilder builder, string name, bool value) =>
        builder.Append(", ").Append(name).Append(" = ").Append(value ? "true" : "false");

    private static void WriteString(StringBuilder builder, string value)
    {
        builder.Append('"');
        foreach (var character in value)
        {
            switch (character)
            {
                case '\b': builder.Append("\\b"); break;
                case '\t': builder.Append("\\t"); break;
                case '\n': builder.Append("\\n"); break;
                case '\f': builder.Append("\\f"); break;
                case '\r': builder.Append("\\r"); break;
                case '"': builder.Append("\\\""); break;
                case '\\': builder.Append("\\\\"); break;
                default:
                    if (character < ' ' || character == '\u007f')
                    {
                        builder.Append("\\u").Append(((int)character).ToString(
                            "X4",
                            CultureInfo.InvariantCulture));
                    }
                    else
                    {
                        builder.Append(character);
                    }

                    break;
            }
        }

        builder.Append('"');
    }
}
