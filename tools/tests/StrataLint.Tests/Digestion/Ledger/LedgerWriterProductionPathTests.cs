using System.Collections.Immutable;
using System.Net;
using System.Net.Sockets;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LedgerWriterProductionPathTests
{
    private const string AlphaGid = "D5/S0/Carrier/Alpha.alpha";
    private const string ZetaGid = "D5/S0/Carrier/Zeta.zeta";

    [Fact]
    public void CoverAtom_AppendWritesCoverageAndScribeReceiptsInOrdinalOrder()
    {
        var definition = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256;
        var emission = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256;
        var inputs = MaterializeSpec() with
        {
            InitialCoverage = [ZetaGid],
            InitialDefinitionSha256 = definition,
            InitialEmissionSha256 = emission,
            Migration = "absorbed",
            Truth = "closed",
            BaselineTargetIdentical = true,
        };
        var world = inputs.Materialize();
        using var repository = new TemporaryDirectory();
        var environment = Environment(repository, world, world.Document, world.Document);

        var result = environment.CoverAtom(
            ["--cover-atom", inputs.AtomId, "--gid", AlphaGid, "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        AssertCanonicalGidBytes(ReadAtomBytes(repository, inputs.AtomId));
    }

    [Fact]
    public async Task DepositDelegatedMultiGidCover_WritesLedgerBytesInOrdinalOrder()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.AddSecondaryFormalization();
        var spec = new CoverSpec
        {
            ModuleGid = "D5/S3/Observer/WindowRegisterCRT",
            Declaration = "window_register_crt_decomposition",
            ReportDeclarations = ["window_register_crt_decomposition"],
            SecondaryTarget = ("D5/S0/Carrier/Probe", "probe"),
        };
        var world = spec.Materialize();
        DirectoryLedgerTestSupport.Write(fixture.Root, world.Files);
        File.Delete(Path.Combine(fixture.Root, TransactionFixture.BackfillPath));
        File.WriteAllText(Path.Combine(fixture.Root, "bin", "make"),
            "#!/usr/bin/env bash\nset -euo pipefail\nprintf 'make:%s\\n' \"$*\" >> \"$PLAYBOOK_TEST_CALLS\"\n",
            new UTF8Encoding(false));
        using var listener = new TcpListener(IPAddress.Loopback, 0);
        listener.Start();
        var port = ((IPEndPoint)listener.LocalEndpoint).Port;
        var dotnet = Path.Combine(fixture.Root, "bin", "dotnet");
        File.Move(dotnet, dotnet + "-stub");
        // Only transport crosses the process boundary. Coverage still runs through
        // CliApplication and ProductionCliEnvironment before deposit can continue.
        File.WriteAllText(dotnet, $$"""
            #!/usr/bin/env bash
            set -euo pipefail
            original=("$@")
            while [[ $# -gt 0 && $1 != -- ]]; do shift; done
            [[ $# -gt 0 ]] || exit 96
            shift
            if [[ ${1:-} != cover-atom ]]; then
              exec "$(dirname "$0")/dotnet-stub" "${original[@]}"
            fi
            printf 'dotnet:%s\n' "$*" >> "$PLAYBOOK_TEST_CALLS"
            exec 3<>/dev/tcp/127.0.0.1/{{port}}
            printf '%s\n' "$@" '' >&3
            IFS= read -r status <&3
            cat <&3
            exit "$status"
            """ + "\n", new UTF8Encoding(false));
        File.SetUnixFileMode(dotnet, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        foreach (var gid in new[] { TransactionFixture.SecondaryGid, TransactionFixture.Gid })
            await DepositThroughCli(fixture, listener, world, spec.AtomId, gid);

        Assert.Equal(
            [TransactionFixture.SecondaryGid, TransactionFixture.Gid],
            fixture.Calls().Where(static call => call.StartsWith("dotnet:cover-atom ", StringComparison.Ordinal))
                .Select(static call => call.Split(' ')[4]));
        var atomPath = Assert.Single(Directory.EnumerateFiles(
            Path.Combine(fixture.Root, BackfillInventoryLoader.RootPath),
            spec.AtomId + ".yaml", SearchOption.AllDirectories));
        AssertCanonicalGidBytes(File.ReadAllBytes(atomPath), TransactionFixture.Gid, TransactionFixture.SecondaryGid);
    }

    private static async Task DepositThroughCli(
        TransactionFixture fixture,
        TcpListener listener,
        CoverInputs world,
        string atomId,
        string gid)
    {
        using var cancellation = new CancellationTokenSource();
        var process = Task.Run(() => fixture.Run("deposit", gid: gid, atomId: atomId,
            timeout: TestBudgets.PlaybookProcessHangGuard));
        var result = await ExchangeDelegatedCover(listener, process, cancellation, arguments =>
        {
            var current = world.Files.Where(static pair => !BackfillInventoryLoader.IsCanonicalPath(pair.Key))
                .ToDictionary(StringComparer.Ordinal);
            foreach (var path in Directory.EnumerateFiles(
                Path.Combine(fixture.Root, BackfillInventoryLoader.RootPath), "*", SearchOption.AllDirectories))
                current[Path.GetRelativePath(fixture.Root, path).Replace(Path.DirectorySeparatorChar, '/')] = File.ReadAllText(path);
            var environment = new ProductionCliEnvironment(
                fixture.Root,
                new FakeRepositoryGateway(RawChangeSet.Create([]), CoverWorld.Raw(current), CoverWorld.Raw(world.Baseline)),
                new FakeLeanReportSource(world.Report),
                new FakeScribeEmissionVerifier(world.VerifiedEmissions),
                CoverWorld.TimeProvider);
            var console = new BufferedConsole();
            var status = CliApplication.Run(arguments, environment, console);
            return (status, console.Output + console.Error);
        });
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains($"COVER atom_id={atomId} gid={gid} ledger_changed=true",
            Encoding.UTF8.GetString(result.StandardOutput), StringComparison.Ordinal);
    }

    [Fact]
    public void AlignScribeReceipt_SeedMissingWritesScribeReceiptsInOrdinalOrder()
    {
        var spec = MaterializeSpec() with { BaselineTargetIdentical = true };
        var world = spec.Materialize();
        var target = Assert.Single(world.Document.RequireDigestionEntries());
        var seedDocument = world.Document.WithDigestionSources(
        [
            Assert.Single(world.Document.RequireDigestionSources()) with
            {
                Entries =
                [
                    target with
                    {
                        Coverage =
                        [
                            new DigestionCoverageEdge(ZetaGid, spec.TargetStatementId),
                            new DigestionCoverageEdge(
                                AlphaGid,
                                FrozenStatementReceiptTestData.Id('c')),
                        ],
                        Receipts = target.Receipts with
                        {
                            Scribe = ImmutableArray<DigestionScribeReceipt>.Empty,
                        },
                        ProjectedStatus = new DigestionStatus(
                            DigestionMigrationState.Partial,
                            DigestionTruthState.Closed),
                    },
                ],
            },
        ]);
        using var repository = new TemporaryDirectory();
        var environment = Environment(repository, world, seedDocument, seedDocument);
        var pairsPath = Path.Combine(repository.Path, "pairs.tsv");
        File.WriteAllText(
            pairsPath,
            $"{spec.AtomId}\t{ZetaGid}\n{spec.AtomId}\t{AlphaGid}\n",
            new UTF8Encoding(false));

        var result = environment.AlignScribeReceipt(
            ["--seed-missing", "--pairs", "pairs.tsv", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        AssertCanonicalGidBytes(ReadAtomBytes(repository, spec.AtomId));
    }

    private static CoverSpec MaterializeSpec() => new()
    {
        ModuleGid = "D5/S0/Carrier/Zeta",
        Declaration = "zeta",
        ReportDeclarations = ["zeta"],
        SecondaryTarget = ("D5/S0/Carrier/Alpha", "alpha"),
    };

    private static ProductionCliEnvironment Environment(
        TemporaryDirectory repository,
        CoverInputs world,
        BackfillInventoryDocument currentDocument,
        BackfillInventoryDocument baselineDocument)
    {
        var currentFiles = new Dictionary<string, string>(world.Files, StringComparer.Ordinal);
        var baselineFiles = new Dictionary<string, string>(world.Baseline, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, currentDocument);
        DirectoryLedgerTestSupport.ReplaceWithProjection(baselineFiles, baselineDocument);
        DirectoryLedgerTestSupport.Write(repository.Path, currentFiles);
        return new ProductionCliEnvironment(
            repository.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(baselineFiles)),
            new FakeLeanReportSource(world.Report),
            new FakeScribeEmissionVerifier(world.VerifiedEmissions),
            CoverWorld.TimeProvider);
    }

    private static byte[] ReadAtomBytes(TemporaryDirectory repository, string atomId)
    {
        var ledgerRoot = Path.Combine(
            repository.Path,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar));
        var path = Assert.Single(Directory.EnumerateFiles(
            ledgerRoot,
            atomId + ".yaml",
            SearchOption.AllDirectories));
        return File.ReadAllBytes(path);
    }

    private static void AssertCanonicalGidBytes(byte[] bytes, string alpha = AlphaGid, string zeta = ZetaGid)
    {
        var text = new UTF8Encoding(false, true).GetString(bytes);
        var receipts = text.IndexOf("receipts:\n", StringComparison.Ordinal);
        var alphaCoverage = text.IndexOf($"  - gid: {alpha}\n", StringComparison.Ordinal);
        var zetaCoverage = text.IndexOf($"  - gid: {zeta}\n", StringComparison.Ordinal);
        var alphaScribe = text.IndexOf(
            $"    - gid: {alpha}\n",
            receipts,
            StringComparison.Ordinal);
        var zetaScribe = text.IndexOf(
            $"    - gid: {zeta}\n",
            receipts,
            StringComparison.Ordinal);

        Assert.True(alphaCoverage >= 0 && alphaCoverage < zetaCoverage && zetaCoverage < receipts, text);
        Assert.True(alphaScribe > receipts && alphaScribe < zetaScribe, text);
    }
}
