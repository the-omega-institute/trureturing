using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    private static string Ledger(IReadOnlyList<string> acknowledgedStale, params string[] entries)
    {
        var acknowledgments = acknowledgedStale.Count == 0
            ? "[]"
            : "\n" + string.Join("\n", acknowledgedStale.Select(static value => "      - " + value));
        return $$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: source
                path: docs/source.md
                atomizer: {{string.Concat("gi", "ct", "-v1")}}
                acknowledged_stale: {{acknowledgments}}
                entries:
            {{string.Join("\n", entries)}}
            ticket_index: []
            """;
    }

    private static string Entry(string atomId, DigestionAtom atom) =>
        Entry(atomId, atom.AstPath, atom.Fingerprints);

    private static string CasEntry(string atomId, DigestionAtom atom, string casRef) => $$"""
              - atom_id: {{atomId}}
                ast_path: {{atom.AstPath}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                cas_ref: {{casRef}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: residual
                  truth: open
        """;

    private static string LegacyEntry(string atomId, DigestionAtom atom) => $$"""
                  - atom_id: {{atomId}}
                    boundary:
                      ast_path: {{atom.AstPath}}
                      start_byte: {{atom.StartByte}}
                      end_byte: {{atom.EndByte}}
                    fingerprints:
                      raw_sha256: {{atom.Fingerprints.RawSha256}}
                      normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                    cas_ref: {{atom.Fingerprints.RawSha256}}
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            """;

    private static string StatusFirstEntry(string atomId, DigestionAtom atom) => $$"""
                  - status:
                      migration: residual
                      truth: open
                    atom_id: {{atomId}}
                    ast_path: {{atom.AstPath}}
                    fingerprints:
                      raw_sha256: {{atom.Fingerprints.RawSha256}}
                      normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                    cas_ref: {{atom.Fingerprints.RawSha256}}
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
            """;

    private static string Entry(
        string atomId,
        string astPath,
        DigestionFingerprints fingerprints) => $$"""
                  - atom_id: {{atomId}}
                    ast_path: {{astPath}}
                    fingerprints:
                      raw_sha256: {{fingerprints.RawSha256}}
                      normalized_sha256: {{fingerprints.NormalizedSha256}}
                    cas_ref: {{fingerprints.RawSha256}}
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            """;
}
