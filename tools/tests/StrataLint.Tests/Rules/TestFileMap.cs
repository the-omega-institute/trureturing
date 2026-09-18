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
        schema_version = 5
        resources = []

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
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"

        [[files]]
        pattern = ".gitignore"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "AGENTS.md"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Blueprint/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "CLAUDE.md"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Chronicle/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "D5/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Directory.Build.props"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"

        [[files]]
        pattern = "Directory.Packages.props"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Evidence/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Generated/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Golden/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Library/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Makefile"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/BACKFILL.yaml"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/Digestion/**"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/FILEMAP.*.toml"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/FILEMAP.toml"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/ReportConsumers/lean-report.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/ReportConsumers/scribe-content.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/ReportProducers/lean-report.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/ReportProducers/scribe-content.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/ci-checks.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/ci-resources.json"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/domains.yaml"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/engineering-projects.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/judge-seed.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Meta/package-materials.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Papers/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Problems/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "README.md"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "Trureturing.lean"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "agents/CONTEXT.md"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "agents/adversary.md"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "docs/CONTRIBUTING.md"
        require = []
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
        require = []
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
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "docs/develop/theory/**"
        require = []
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
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "lake-manifest.json"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "lakefile.toml"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "lean-report-inputs.json"
        require = []
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["lean-inspector"]
        verified_by = ["LeanReportSelection"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "lean-toolchain"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"


        [[files]]
        pattern = "tools/**"
        require = []
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        """ + "\n";
}
