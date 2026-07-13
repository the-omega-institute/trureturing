namespace StrataLint.Tests;

internal static class TestRegistry
{
    internal const string Canonical = """
        schema_version: 1
        root_files:
          - ".gitignore"
          - "AGENTS.md"
          - "CLAUDE.md"
          - "Directory.Build.props"
          - "Directory.Packages.props"
          - "Makefile"
          - "README.md"
          - "Trureturing.lean"
          - "global.json"
          - "lake-manifest.json"
          - "lakefile.toml"
          - "lean-toolchain"
        governance_documents:
          - "docs/CONTRIBUTING.md"
          - "docs/GOVERNANCE.md"
          - "docs/develop/spec/golden-ledger-repo-spec.md"
          - "docs/develop/theory/GICT_complete_development_v3_3.md"
          - "docs/develop/theory/PZG_BEDC_kernel_formal_170.md"
        agent_files:
          - "CONTEXT.md"
          - "adversary.md"
        artifact_kinds:
          json:
            profile: structured-json
            selectors:
              - "check"
              - "legacy"
              - "quote"
              - "result"
              - "run"
            path_selectors:
              - "formal"
              - "values"
          yaml:
            profile: structured-yaml
            selectors:
              - "result"
              - "run"
              - "spec"
            path_selectors:
              - "experiments"
              - "formal"
        """ + "\n";

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
}
