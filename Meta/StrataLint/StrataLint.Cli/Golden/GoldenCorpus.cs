namespace StrataLint.Cli;

internal sealed record GoldenCase(
    string Name,
    IReadOnlyList<GoldenMutation> BaselineMutations,
    IReadOnlyList<GoldenMutation> Mutations,
    IReadOnlyList<GoldenDiagnostic> ExpectedDiagnostics,
    IReadOnlyList<string> Changes);

internal sealed record GoldenDiagnostic(int RuleNumber, string Path, string Message);

internal sealed record GoldenCorpusFile(string Path, IReadOnlyList<GoldenCase> Cases);

internal sealed class GoldenCorpusSet
{
    internal GoldenCorpusSet(IReadOnlyList<GoldenCorpusFile> files)
    {
        Files = files;
        Cases = files.SelectMany(static file => file.Cases).ToArray();
    }

    internal IReadOnlyList<GoldenCorpusFile> Files { get; }

    internal IReadOnlyList<GoldenCase> Cases { get; }
}

internal enum GoldenGenerality
{
    General,
    Instance,
    Extremal,
}

internal enum GoldenStratum
{
    S0,
    S1,
    S2,
    S3,
    S4,
}

internal abstract record GoldenMutation
{
    internal sealed record Write(string Path, string Content) : GoldenMutation;

    internal sealed record WriteParts(string Path, IReadOnlyList<string> Parts) : GoldenMutation;

    internal sealed record Lean(
        string Path,
        string RawGid,
        GoldenGenerality Generality,
        string Body) : GoldenMutation;

    internal sealed record Delete(string Path) : GoldenMutation;

    internal sealed record AppendLines(string Path, int Count, string Line) : GoldenMutation;

    internal sealed record AddDomain(string Name, GoldenStratum Stratum) : GoldenMutation;

    internal sealed record AddTask(string Path, string RawGid, string RawCaseId) : GoldenMutation;

    internal sealed record PopulateDirectory : GoldenMutation;

    internal sealed record EmptyMirrorWaiver : GoldenMutation;

    internal sealed record EvidenceMirror(bool IncludeJson, bool IncludeYaml) : GoldenMutation;

    internal sealed record ReplaceBackfill(string OldValue, string NewValue) : GoldenMutation;

    internal sealed record ReplaceFirstBackfillDisposition(string RawGid) : GoldenMutation;

    internal sealed record MutateBackfillAnchor(string Anchor, bool Duplicate) : GoldenMutation;
}

internal static partial class GoldenCorpus
{
    internal const string FixtureRegistry = """
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

    internal const string FixtureDigestionSourcePath = "docs/GOVERNANCE.md";
    internal const string FixtureDigestionSource = "x";
    internal const string FixtureAtomId = "fixture-atom";

    internal const string FixtureBackfill = """
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: fixture-source
            path: docs/GOVERNANCE.md
            atomizer: none
            entries:
              - atom_id: fixture-atom
                boundary:
                  ast_path: manual/fixture
                  start_byte: 0
                  end_byte: 1
                fingerprints:
                  raw_sha256: sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881
                  normalized_sha256: sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881
                coverage_gids:
                  - D5/S0/Carrier/BackfillTarget
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: partial
                  truth: closed
        ticket_index:
          - case_id: D5-T0001
            gid: D5/X_Frontier/HeartsDraft
          - case_id: D5-T0002
            gid: D5/X_Frontier/StrataLintLeanEnvironment
          - case_id: D5-T0003
            gid: D5/X_Frontier/ValuesProducer
          - case_id: D5-T0004
            gid: D5/X_Frontier/SplitTool
          - case_id: D5-T0005
            gid: D5/X_Frontier/PaperGenerator
          - case_id: D5-T0006
            gid: D5/X_Frontier/D5P001
          - case_id: D5-T0007
            gid: D5/X_Frontier/RequiredChecks
          - case_id: D5-T0008
            gid: D5/X_Frontier/GoldenUnitsUFD
          - case_id: D5-T0009
            gid: D5/X_Frontier/FutureInstances
          - case_id: D5-T0010
            gid: D5/X_Frontier/ToolchainUpgrade
          - case_id: D5-T0011
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0012
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0013
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0014
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0015
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0016
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0017
            gid: D5/X_Frontier/RequiredChecks
          - case_id: D5-T0018
            gid: D5/X_Frontier/HeartsDraft
        """ + "\n";

    internal const string FixtureDomains = """
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

    internal const string RingPath = "D5/S0/Carrier/Ring.lean";
    internal const string BlueprintPath = "Blueprint/D5/S0/Carrier/Ring.md";
    internal const string NotationPath = "D5/S0/Conventions/Notation.lean";
    internal const string AssumptionDebtPath = "D5/X_Assumptions/AxiomDebt.lean";
    internal const string HeartsPath = "D5/X_Frontier/Hearts.lean";
    internal const string SyntheticProtectedPath =
        "Meta/StrataLint/StrataLint.Engine/SyntheticProtected.cs";

}
