namespace StrataLint.Engine;

/// Strict scoped-report entry point.  The parser and material checks are shared
/// with <see cref="RawLeanReportArtifact"/>; this type exists so a full-mode
/// caller cannot accidentally accept the scoped schema.
internal static class ScopedLeanReportArtifact
{
    internal const string Schema = "stratalint-scoped-lean-report-v1";

    internal static LeanAxiomReport Read(
        ReadOnlySpan<byte> bytes,
        LeanReportScope scope) =>
        RawLeanReportArtifact.ReadForScope(bytes, scope);

    internal static LeanAxiomReport ReadFile(
        string path,
        LeanReportScope scope,
        bool validateMaterials = false) =>
        RawLeanReportArtifact.ReadFileForScope(path, scope, validateMaterials);
}
