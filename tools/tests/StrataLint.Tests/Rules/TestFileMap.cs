using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class TestFileMap
{
    internal static readonly string Canonical = Encoding.UTF8.GetString(FileMapCanonicalWriter.Write(
        FileMapLoader.Parse(Encoding.UTF8.GetBytes(Input), "synthetic FILEMAP")).AsSpan());

    internal const string Domains = """
        domains:
          Carrier:
            stratum: S0
            definition: The golden integer carrier.
          Conventions:
            stratum: S0
            definition: Canonical W-digit conventions.
          Phase:
            stratum: S1
            definition: Additive golden-ratio phases modulo one.
          Weil:
            stratum: S3
            definition: Classical zeta conventions and Weil test functions.
        """ + "\n";


    private const string Input = """
        schema_version = 3

        [residence_policy]
        case_id = "TEST"
        desired = "data-must-live-outside-tools"
        known_violation_count = 0
        status = "closed"

        [evidence.artifact_kinds."csv"]
        profile = "opaque-text"
        selectors = ["result"]
        path_selectors = ["formal"]

        [evidence.artifact_kinds."json"]
        profile = "structured-json"
        selectors = ["check", "legacy", "quote", "result", "run"]
        path_selectors = ["experiments", "formal", "kernels", "special", "values"]

        [evidence.artifact_kinds."md"]
        profile = "opaque-text"
        selectors = ["result"]
        path_selectors = ["formal", "special"]

        [evidence.artifact_kinds."py"]
        profile = "opaque-text"
        selectors = ["source"]
        path_selectors = ["formal", "kernels"]

        [evidence.artifact_kinds."txt"]
        profile = "opaque-text"
        selectors = ["result"]
        path_selectors = ["formal"]

        [evidence.artifact_kinds."yaml"]
        profile = "structured-yaml"
        selectors = ["result", "run", "spec"]
        path_selectors = ["experiments", "formal"]

        [evidence.artifact_kinds."yml"]
        profile = "structured-yaml"
        selectors = ["result", "run", "spec"]
        path_selectors = ["experiments", "formal"]


        [[files]]
        pattern = ".github/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"

        [[files]]
        pattern = ".gitignore"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "AGENTS.md"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Blueprint/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "CLAUDE.md"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Chronicle/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "D5/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Directory.Build.props"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Directory.Packages.props"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Evidence/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Generated/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Golden/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Library/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Makefile"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Papers/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Problems/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "README.md"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Trureturing.lean"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "agents/CONTEXT.md"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "agents/adversary.md"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "docs/CONTRIBUTING.md"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        digestion_source = true


        [[files]]
        pattern = "docs/GOVERNANCE.md"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        digestion_source = true


        [[files]]
        pattern = "docs/develop/spec/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "docs/develop/theory/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        digestion_source = true


        [[files]]
        pattern = "global.json"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "lake-manifest.json"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "lakefile.toml"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "lean-toolchain"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "tools/**"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        """ + "\n";
}
