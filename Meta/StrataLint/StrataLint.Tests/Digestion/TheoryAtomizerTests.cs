using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoryAtomizerTests
{
    private const string FirstProductionSource =
        "docs/develop/theory/GICT_complete_development_v3_3.md";
    private const string SecondProductionSource =
        "docs/develop/theory/PZG_BEDC_kernel_formal_170.md";

    public static TheoryData<string, string, int> ProductionTheorySources => new()
    {
        { FirstProductionSource, AtomizerRegistry.GictId, 61 },
        { SecondProductionSource, AtomizerRegistry.PzgId, 526 },
    };

    [Fact]
    public void RegistryFailsClosedForAnUnknownAtomizerAndListsRegisteredIds()
    {
        const string unknown = "unregistered-v1";

        var error = Assert.Throws<FormatException>(() =>
            AtomizerRegistry.Atomize(unknown, Array.Empty<byte>()));

        Assert.Equal(
            $"Unknown atomizer id '{unknown}'. Registered atomizers: "
            + string.Join(", ", AtomizerRegistry.RegisteredIds)
            + ".",
            error.Message);
    }

    [Fact]
    public void GictAdapterBuildsClaimWithHeadingScaffoldAndReassemblesExactBytes()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n## VII.7 接口\r\n\r\n"
            + "**定理 7.15(G 轴质量)**〔定理·证〕。黄金频率最优。\r\n\r\n"
            + "*证明*。证毕。\r\n\r\n尾注。\r\n");

        var document = GictAtomizer.Atomize(bytes);
        var atom = Assert.Single(document.Claims);

        Assert.Equal("theorem/7.15", atom.AstPath);
        Assert.Equal(["GICT", "VII.7 接口"], atom.Context.Select(static item => item.Text));
        Assert.Equal(bytes, document.Reassemble().ToArray());
        Assert.Matches("^sha256:[0-9a-f]{64}$", atom.Fingerprints.RawSha256);
        Assert.Matches("^sha256:[0-9a-f]{64}$", atom.Fingerprints.NormalizedSha256);
    }

    [Fact]
    public void PzgAdapterSeparatesClosedTheoremAndOpenLedgerClaim()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n## 第二十六章 桥通道\n\n"
            + "**定理 26.3(桥通道)**〔closed〕。通道存在。\n\n"
            + "**账目 26.4(RH 的三面孔)**〔open〕。正性未知。\n");

        var document = PzgAtomizer.Atomize(bytes);

        Assert.Equal(["theorem/26.3", "ledger/26.4"], document.Claims.Select(static item => item.AstPath));
        Assert.All(document.Claims, atom =>
            Assert.Equal(["PZG", "第二十六章 桥通道"], atom.Context.Select(static item => item.Text)));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void GictAdapterTreatsEachAppendixConstantRowAsAnAtomicClaim()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n## 附录 A:常数总表\n\n"
            + "| 常数 | 值 |\n|---|---|\n"
            + "| κ | 1/(2φ) |\n"
            + "| C₀ | φ/2 |\n"
            + "| **C_φ** | 0.045 |\n");

        var document = GictAtomizer.Atomize(bytes);

        Assert.Equal(
            ["constant/kappa", "constant/C0", "constant/Cphi"],
            document.Claims.Select(static item => item.AstPath));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgAdapterTreatsOpenLedgerItemsAsAtomicClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n## 第二十九章 开放账本\n\n"
            + "**O-5**〔open〕发动机未闭。\n"
            + "**O-6**〔open〕正性未闭。\n");

        var document = PzgAtomizer.Atomize(bytes);

        Assert.Equal(["open/O-5", "open/O-6"], document.Claims.Select(static item => item.AstPath));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void GictAdapterIdentifiesNumberedNotesAsClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**注 2.5(Why five)**。claim。\n");

        var atom = Assert.Single(GictAtomizer.Atomize(bytes).Claims);

        Assert.Equal("note/2.5", atom.AstPath);
    }

    [Fact]
    public void PzgAdapterIdentifiesEveryProductionNumberedClaimKind()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n"
            + "**后果 7.4**。a。\n\n"
            + "**原则 14.3**。b。\n\n"
            + "**规格 20.2**。c。\n\n"
            + "**契约 23.1**。d。\n\n"
            + "**定理形 6.190**。e。\n\n"
            + "**前沿引注 6.56**。f。\n\n"
            + "**延表 6.38′**。g。\n\n"
            + "**路线 21.1**。h。\n\n"
            + "**〔27.82 追注:receipt〕**。i。\n");

        var document = PzgAtomizer.Atomize(bytes);

        Assert.Equal(
            [
                "consequence/7.4",
                "principle/14.3",
                "specification/20.2",
                "contract/23.1",
                "theorem-form/6.190",
                "frontier-note/6.56",
                "extension-table/6.38′",
                "route/21.1",
                "trace-note/27.82",
            ],
            document.Claims.Select(static item => item.AstPath));
    }

    [Fact]
    public void RestrictedNormalizationChangesOnlyBomLineEndingsAndUnicodeNormalization()
    {
        var decomposed = "\uFEFFCafe\u0301  \r\nnext\rline\n";
        var composed = "Caf\u00e9  \nnext\nline\n";
        var first = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(decomposed));
        var second = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(composed));

        Assert.NotEqual(first.RawSha256, second.RawSha256);
        Assert.Equal(first.NormalizedSha256, second.NormalizedSha256);
    }

    [Fact]
    public void DuplicateClaimLocatorIsAmbiguousAndFailsClosed()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 7.15(A)**。一。\n\n**定理 7.15(B)**。二。\n");

        var document = GictAtomizer.Atomize(bytes);
        var error = Assert.Throws<FormatException>(() => document.ResolveClaim("theorem/7.15"));

        Assert.Contains("ambiguous", error.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void UnknownNumberedClaimKindFailsClosed()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**猜想 1.1(Unknown kind)**。claim。\n");

        var error = Assert.Throws<FormatException>(() => PzgAtomizer.Atomize(bytes));

        Assert.Contains("unknown PZG numbered claim kind", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GictIngestionSubtractsNormalizedMatchAndAdmitsSemanticRewriteAsResidual()
    {
        var oldBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n**定理 1.1(Test)**。claim。\r\n\r\n*证明*。done。\r\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var ledger = new[] { LedgerEntry("gict-old", AtomizerRegistry.GictId, oldAtom) };
        var lineEndingOnly = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n\n*证明*。done。\n");

        var seen = TheoryIngestion.AdmitResidual(
            AtomizerRegistry.GictId,
            lineEndingOnly,
            ledger);

        var match = Assert.Single(seen.Seen);
        Assert.Equal("gict-old", match.LedgerAtomId);
        Assert.Equal(DigestionFingerprintMatch.Normalized, match.Match);
        Assert.Empty(seen.Residual);

        var rewritten = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。semantically rewritten claim。\n");
        var admitted = TheoryIngestion.AdmitResidual(
            AtomizerRegistry.GictId,
            rewritten,
            ledger);

        Assert.Empty(admitted.Seen);
        var residual = Assert.Single(admitted.Residual);
        Assert.Equal(DigestionMigrationState.Residual, residual.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, residual.ProjectedStatus.Truth);
        Assert.NotEqual(oldAtom.Fingerprints.RawSha256, residual.Atom.Fingerprints.RawSha256);
        Assert.Equal(
            "gict-residual-" + residual.Atom.Fingerprints.RawSha256["sha256:".Length..],
            residual.SuggestedAtomId);
    }

    [Fact]
    public void PzgIngestionSubtractsRawMatchAndAdmitsNewClaim()
    {
        var oldBytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.1(Test)**〔closed〕。claim。\n");
        var oldAtom = Assert.Single(PzgAtomizer.Atomize(oldBytes).Claims);
        var ledger = new[] { LedgerEntry("pzg-old", AtomizerRegistry.PzgId, oldAtom) };

        var seen = TheoryIngestion.AdmitResidual(AtomizerRegistry.PzgId, oldBytes, ledger);
        var incoming = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.2(New)**〔open〕。new claim。\n");
        var admitted = TheoryIngestion.AdmitResidual(AtomizerRegistry.PzgId, incoming, ledger);

        Assert.Equal(DigestionFingerprintMatch.Raw, Assert.Single(seen.Seen).Match);
        Assert.Empty(seen.Residual);
        Assert.Equal("theorem/1.2", Assert.Single(admitted.Residual).Atom.AstPath);
    }

    [Fact]
    public void IngestionFailsClosedWhenOneAtomMatchesMultipleLedgerReceipts()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(bytes).Claims);
        var ledger = new[]
        {
            LedgerEntry("gict-first", AtomizerRegistry.GictId, atom),
            LedgerEntry("gict-second", AtomizerRegistry.GictId, atom),
        };

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(AtomizerRegistry.GictId, bytes, ledger));

        Assert.Contains("ambiguous", error.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void IngestionFailsClosedWhenOneLedgerReceiptMatchesMultipleIncomingAtoms()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n");
        var first = GictAtomizer.Atomize(bytes).Claims[0];
        var ledger = new[] { LedgerEntry("gict-kappa", AtomizerRegistry.GictId, first) };

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(AtomizerRegistry.GictId, bytes, ledger));

        Assert.Contains("matches multiple incoming atoms", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestionFailsClosedForDuplicateResidualFingerprint()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n");

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(
                AtomizerRegistry.GictId,
                bytes,
                Array.Empty<DigestionLedgerEntry>()));

        Assert.Contains("duplicate raw residual fingerprint", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestionFailsClosedForDuplicateNormalizedResidualFingerprint()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\r\n| κ | 1 |\n");
        var claims = GictAtomizer.Atomize(bytes).Claims;
        Assert.Equal(2, claims.Length);
        Assert.NotEqual(claims[0].Fingerprints.RawSha256, claims[1].Fingerprints.RawSha256);
        Assert.Equal(claims[0].Fingerprints.NormalizedSha256, claims[1].Fingerprints.NormalizedSha256);

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(
                AtomizerRegistry.GictId,
                bytes,
                Array.Empty<DigestionLedgerEntry>()));

        Assert.Contains("duplicate normalized residual fingerprint", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ProductionTheorySources))]
    public void ProductionTheoryDocumentReassemblesByteExact(
        string relativePath,
        string atomizerId,
        int expectedClaims)
    {
        var root = FindRepositoryRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, relativePath));

        var document = AtomizerRegistry.Atomize(atomizerId, bytes);

        Assert.Equal(expectedClaims, document.Claims.Length);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "Meta", "BACKFILL.yaml")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }

    private static DigestionLedgerEntry LedgerEntry(
        string atomId,
        string atomizer,
        DigestionAtom atom) => new(
        atomizer,
        "docs/source.md",
        atomizer,
        atomId,
        new DigestionBoundary(atom.AstPath, atom.StartByte, atom.EndByte),
        atom.Fingerprints,
        [],
        new DigestionReceipts([], [], [], [], null),
        new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open));
}
