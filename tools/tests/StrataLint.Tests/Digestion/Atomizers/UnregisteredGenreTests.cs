using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// Where the refusal of an unregistered genre token belongs.
///
/// It used to live in the parser, which threw; ingest caught the throw and replaced the
/// entire volume with one <c>coarse/source</c> atom — and exited zero. So one unwritten word
/// cost pzg-v170 all 1354 of its addressed claims, and the run reported success. The lexicon
/// was acting as a gate on a document it does not own, and the gate leaked.
///
/// The invariant is real — every genre token must be registered — but it belongs to the
/// layer that admits atoms, not to the one that reads bytes. So the parser addresses the
/// claim by its own token and records it, and the ledger refuses. Both axes get stronger:
/// the structure survives, and the run now fails instead of succeeding with a blob.
/// </summary>
public sealed class UnregisteredGenreTests
{
    private static string[] Paths(AtomizedTheoryDocument document) =>
        document.Claims.Select(static claim => claim.AstPath).ToArray();

    [Fact]
    public void PzgAddressesAnUnregisteredNumberedGenreByItsOwnToken()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.1(甲)**。一。\n\n**未登记体 2.3(乙)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(["theorem/1.1", "未登记体/2.3"], Paths(document));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void GictAddressesAnUnregisteredNumberedGenreByItsOwnToken()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(甲)**。一。\n\n**未登记体 2.3(乙)**。二。\n");

        var document = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(["theorem/1.1", "未登记体/2.3"], Paths(document));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ADeclaredDialectAddressesAnUnregisteredGenreByItsOwnToken()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n## 定理 22.2\n\n证。\n\n## 未登记体 3.4\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        Assert.Equal(["theorem/22.2", "未登记体/3.4"], Paths(document));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ObserverUnregisteredClaimLeadIsALedgerFindingWithoutACoarseFallback()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** known。\n\n**新判词。** unknown。\n");

        var alignment = Align(AtomizerRegistry.ObserverId, bytes);

        var finding = Assert.Single(alignment.Findings);
        Assert.Contains("uses claim genres its dialect does not register", finding, StringComparison.Ordinal);
        Assert.Contains("**新判词。**", finding, StringComparison.Ordinal);
        Assert.Empty(alignment.Fallbacks);
        Assert.Empty(alignment.Residual);
    }

    [Fact]
    public void ObserverDuplicateClaimLocatorStillTakesTheCoarsePath()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n"
            + "**定理(观察者代数的唯一形态)。** first。\n\n"
            + "**定理(观察者代数的唯一形态)。** second。\n");

        var alignment = Align(AtomizerRegistry.ObserverId, bytes);

        Assert.Empty(alignment.Findings);
        Assert.Contains(
            "duplicate observer claim locator",
            Assert.Single(alignment.Fallbacks).Reason,
            StringComparison.Ordinal);
        Assert.Equal("coarse/source", Assert.Single(alignment.Residual).Atom.AstPath);
    }

    [Fact]
    public void ConeUnregisteredClaimGenreIsALedgerFindingWithoutACoarseFallback()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**引理 3.5(已登记标题)[证]。**known。\n\n"
            + "**猜想 3.6(未登记标题)[证]。**unknown。\n");

        var alignment = Align(AtomizerRegistry.ConeId, bytes);

        var finding = Assert.Single(alignment.Findings);
        Assert.Contains("uses claim genres its dialect does not register", finding, StringComparison.Ordinal);
        Assert.Contains("猜想", finding, StringComparison.Ordinal);
        Assert.Empty(alignment.Fallbacks);
        Assert.Empty(alignment.Residual);
    }

    [Fact]
    public void ConeMalformedRegisteredClaimTitleStillTakesTheCoarsePath()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第一章 路径散度理论\n\n"
            + "**命题 1.1 未知标题**\n");

        var alignment = Align(AtomizerRegistry.ConeId, bytes);

        Assert.Empty(alignment.Findings);
        Assert.Contains(
            "unknown cone numbered claim title",
            Assert.Single(alignment.Fallbacks).Reason,
            StringComparison.Ordinal);
        Assert.Equal("coarse/source", Assert.Single(alignment.Residual).Atom.AstPath);
    }

    /// <summary>The cost this moves off the volume: its other claims survive the unknown word.</summary>
    [Fact]
    public void OneUnregisteredTokenDoesNotCostTheVolumeItsOtherClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.1**。一。\n\n**未登记体 2.1**。二。\n\n**引理 3.1**。三。\n");

        Assert.Equal(
            ["theorem/1.1", "未登记体/2.1", "lemma/3.1"],
            Paths(PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules)));
    }

    [Fact]
    public void ARegisteredGenreIsStillNormalizedToItsCanonicalKind()
    {
        var bytes = Encoding.UTF8.GetBytes("# PZG\n\n**引理 3.1**。三。\n");

        Assert.Equal(["lemma/3.1"], Paths(PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules)));
    }

    /// <summary>Named once each and deduplicated, which is what the throw path used to give.</summary>
    [Fact]
    public void EveryUnregisteredGenreTokenIsCarriedOnTheDocumentOnce()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**未登记体 2.1**。二。\n\n**另一体 4.1**。四。\n\n**未登记体 5.1**。五。\n");

        Assert.Equal(
            ["另一体", "未登记体"],
            PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules).UnregisteredGenres.ToArray());
    }

    [Fact]
    public void ADocumentWithNoUnregisteredGenreCarriesNone()
    {
        var bytes = Encoding.UTF8.GetBytes("# PZG\n\n**定理 1.1**。一。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(GenreRegistryCheckKind.Collected, document.GenreRegistryCheck.Kind);
        Assert.Empty(document.UnregisteredGenres);
    }

    private static DigestionLedgerAlignment Align(string atomizerId, byte[] bytes)
    {
        var ledger = BackfillInventoryLoader.Load(DigestionTestSupport.EmptyLedger(atomizerId));
        return DigestionLedgerAligner.Evaluate(
            ledger,
            DigestionTestSupport.Snapshot(("docs/source.md", bytes)),
            ledger,
            DigestionAlignmentMode.Ingest);
    }
}
