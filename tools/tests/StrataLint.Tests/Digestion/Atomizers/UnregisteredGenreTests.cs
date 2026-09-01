using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// Where the open accounting of an unregistered genre token belongs.
///
/// It used to live in the parser, which threw; ingest caught the throw and replaced the
/// entire volume with one <c>coarse/source</c> atom — and exited zero. So one unwritten word
/// cost pzg-v170 all 1354 of its addressed claims, and the run reported success. The lexicon
/// was acting as a gate on a document it does not own, and the gate leaked.
///
/// Registration debt belongs to the ledger rather than the byte reader. The parser addresses
/// the claim by its own token, and the ledger admits it only with an exact open projection.
/// Both axes remain explicit: the structure survives, and omission of the debt still fails.
/// </summary>
public sealed class UnregisteredGenreTests
{
    private static void AssertContentIdentities(IEnumerable<DigestionAtom> atoms, int expectedCount)
    {
        var materialized = atoms.ToArray();
        Assert.Equal(expectedCount, materialized.Length);
        Assert.All(materialized, static atom => Assert.Equal(
            DigestionFingerprint.Compute(atom.RawBytes.AsSpan()).RawSha256,
            atom.Fingerprints.RawSha256));
    }

    [Fact]
    public void PzgAddressesAnUnregisteredNumberedGenreInTheReservedNamespace()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.1(甲)**。一。\n\n**未登记体 2.3(乙)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document.Claims, 2);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void GictAddressesAnUnregisteredNumberedGenreInTheReservedNamespace()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(甲)**。一。\n\n**未登记体 2.3(乙)**。二。\n");

        var document = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document.Claims, 2);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ADeclaredDialectAddressesAnUnregisteredGenreInTheReservedNamespace()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n## 定理 22.2\n\n证。\n\n## 未登记体 3.4\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document.Claims, 2);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ObserverUnregisteredClaimLeadIsAdmittedWithoutACoarseFallback()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** known。\n\n**新判词。** unknown。\n");

        var alignment = Align(AtomizerRegistry.ObserverId, bytes);

        Assert.Empty(alignment.Findings);
        Assert.Empty(alignment.Fallbacks);
        Assert.Equal(2, alignment.Residual.Length);
        AssertContentIdentities(alignment.Residual.Select(static item => item.Atom), 2);
        Assert.Contains(alignment.Residual, static item =>
            Encoding.UTF8.GetString(item.Atom.RawBytes.AsSpan())
                .Contains("**新判词。**", StringComparison.Ordinal));
        Assert.Equal(
            ["**新判词。**"],
            alignment.GenreRegistryChecks["source"].UnregisteredGenres.ToArray());
    }

    [Fact]
    public void ObserverUsesTheSharedUnregisteredNamespace()
    {
        var bytes = Encoding.UTF8.GetBytes("# Observer\n\n**新判词。** unknown。\n");

        var document = ObserverAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document.Claims, 1);
    }

    [Fact]
    public void ObserverRepeatedClaimLeadProducesDistinctContentAtoms()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n"
            + "**定理(观察者代数的唯一形态)。** first。\n\n"
            + "**定理(观察者代数的唯一形态)。** second。\n");

        var alignment = Align(AtomizerRegistry.ObserverId, bytes);

        Assert.Empty(alignment.Findings);
        Assert.Empty(alignment.Fallbacks);
        AssertContentIdentities(alignment.Residual.Select(static item => item.Atom), 2);
        Assert.Equal(
            2,
            alignment.Residual.Select(static item => item.Atom.Fingerprints.RawSha256)
                .Distinct(StringComparer.Ordinal).Count());
    }

    [Fact]
    public void ConeUnregisteredClaimGenreIsAdmittedWithoutACoarseFallback()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**引理 3.5(已登记标题)[证]。**known。\n\n"
            + "**猜想 3.6(未登记标题)[证]。**unknown。\n");

        var alignment = Align(AtomizerRegistry.ConeId, bytes);

        Assert.Empty(alignment.Findings);
        Assert.Empty(alignment.Fallbacks);
        Assert.Equal(2, alignment.Residual.Length);
        AssertContentIdentities(alignment.Residual.Select(static item => item.Atom), 2);
        Assert.Contains(alignment.Residual, static item =>
            Encoding.UTF8.GetString(item.Atom.RawBytes.AsSpan())
                .Contains("**猜想 3.6", StringComparison.Ordinal));
        Assert.Equal(
            ["猜想"],
            alignment.GenreRegistryChecks["source"].UnregisteredGenres.ToArray());
    }

    [Fact]
    public void ConeUsesTheSharedUnregisteredNamespace()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**猜想 3.6(未登记标题)[证]。**unknown。\n");

        var document = ConeAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document.Claims, 1);
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
        AssertContentIdentities(alignment.Residual.Select(static item => item.Atom), 1);
    }

    /// <summary>The cost this moves off the volume: its other claims survive the unknown word.</summary>
    [Fact]
    public void OneUnregisteredTokenDoesNotCostTheVolumeItsOtherClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.1**。一。\n\n**未登记体 2.1**。二。\n\n**引理 3.1**。三。\n");

        AssertContentIdentities(PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims, 3);
    }

    [Fact]
    public void ARegisteredGenreIsStillNormalizedToItsCanonicalKind()
    {
        var bytes = Encoding.UTF8.GetBytes("# PZG\n\n**引理 3.1**。三。\n");

        AssertContentIdentities(PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims, 1);
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
        var ledger = DigestionTestSupport.EmptyDocument(atomizerId);
        return DigestionLedgerAligner.Evaluate(
            ledger,
            DigestionTestSupport.Snapshot(("docs/source.md", bytes)),
            ledger,
            DigestionAlignmentMode.Ingest);
    }
}
