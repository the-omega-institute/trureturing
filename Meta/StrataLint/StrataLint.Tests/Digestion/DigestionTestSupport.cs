using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class DigestionTestSupport
{
    internal static string EmptyLedger(string atomizerId) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: source
            path: docs/source.md
            atomizer: {{atomizerId}}
            entries: []
        ticket_index: []
        """;

    internal static string ReceiptList(string key, string value, int spaces) => value == "[]"
        ? new string(' ', spaces) + key + ": []"
        : new string(' ', spaces) + key + ":\n" + Indent(value, spaces + 2);

    private static string Indent(string value, int spaces) => string.Join(
        '\n',
        value.Split('\n').Select(line => new string(' ', spaces) + line));

    internal static RepositorySnapshot Snapshot(params (string Path, byte[] Bytes)[] files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(file => new RawRepositoryEntry(
            file.Path,
            ImmutableArray.CreateRange(file.Bytes))));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    internal static RepositorySnapshot Snapshot(
        byte[] sourceBytes,
        IEnumerable<DigestionCasObject> casObjects) => Snapshot(
            casObjects
                .Select(static item => (item.RelativePath, item.Bytes.ToArray()))
                .Prepend(("docs/source.md", sourceBytes))
                .ToArray());

    internal static (string Path, byte[] Bytes) CasFile(DigestionAtom atom) =>
        (DigestionCasStore.RootPath + atom.Fingerprints.RawSha256["sha256:".Length..],
            atom.RawBytes.ToArray());

    internal static AcceptedLeanClosure AcceptedLean(params string[] paths) => AcceptedLean(
        paths.Select(path => (path, new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("probe", "theorem", "True", ImmutableArray<string>.Empty)]))).ToArray());

    internal static AcceptedLeanClosure AcceptedLean(
        params (string Path, LeanFileReport Report)[] reports) =>
        AcceptedLeanClosure.Create(LeanAxiomReport.Create(reports.ToDictionary(
            static item => item.Path,
            static item => item.Report,
            StringComparer.Ordinal)));

    internal static string Lean(string gid) => $$"""
        /- GID: {{gid}}
           generality: G
           mirror-B: none(waiver:test)
           mirror-E: none(waiver:test)
           anchors: []
           digest: Digestion test fixture. -/
        theorem probe : True := by trivial
        """;
}
