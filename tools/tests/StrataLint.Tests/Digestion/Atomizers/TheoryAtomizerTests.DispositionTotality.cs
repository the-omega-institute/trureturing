using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    private static readonly TheoryAtomizerRules DispositionRules = new(
        observerClaimPrefixes: [new AtomizerMapping("**Known**", "theorem/known")],
        coneClaimPrefixes:
        [
            new AtomizerMapping("定理", "theorem/{number}|theorem-form/{number}"),
            new AtomizerMapping("定义", "definition/{number}"),
        ],
        gictGenres:
        [
            new AtomizerMapping("定理", "theorem"),
            new AtomizerMapping("定义", "definition"),
        ],
        gictClaimPrefixes: [new AtomizerMapping("**Heart**", "open/heart")],
        gictConstants: [new AtomizerMapping("κ", "constant/kappa")],
        pzgGenres:
        [
            new AtomizerMapping("定理", "theorem"),
            new AtomizerMapping("定义", "definition"),
            new AtomizerMapping("评注", "remark"),
        ],
        pzgMarkers: ImmutableDictionary<string, string>.Empty
            .Add("trace-note", "追注"),
        pzgHeadingPrefixes:
        [
            new AtomizerMapping("Supplement", "metadata/supplement"),
            new AtomizerMapping("判负册", "negative-register/batch"),
        ],
        wmHeadings: ImmutableDictionary<string, string>.Empty
            .Add("title", "世界模型账本卷:公理纲要(BEDC-WM)")
            .Add("appendix", "§7-附 尸检账(只增不删)")
            .Add("audit", "校核记录(append-only,按版分块)"),
        dialects: ImmutableDictionary<string, DeclaredDialect>.Empty.Add(
            "qdo",
            new DeclaredDialect(
                "qdo",
                "^(?<kind>\\p{L}+)\\s+(?<number>[0-9]+(?:\\.[0-9]+)+)",
                [new AtomizerMapping("定理", "theorem")],
                [],
                HeadingClaims: true)));

    [Fact]
    public void MarkdownAstGenericLocatorProducerEmitsOnlyResolvableKinds()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Overview\n\nIntro.\n\n## 定理 1.1\n\nClaim.\n\n**2.1** item.\n");

        AssertEveryEmittedKindResolves(AtomizerRegistry.GenericId, bytes, TheoryAtomizerRules.None);
    }

    [Fact]
    public void NumberedClaimProducersForGictAndPzgEmitOnlyResolvableKinds()
    {
        var gict = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1**。known。\n\n**未登记体 2.2**。unknown。\n");
        var pzg = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.1**。known。\n\n**未登记体 2.2**。unknown。\n");

        AssertEveryEmittedKindResolves(AtomizerRegistry.GictId, gict, DispositionRules);
        AssertEveryEmittedKindResolves(AtomizerRegistry.PzgId, pzg, DispositionRules);
    }

    [Fact]
    public void ConeProducerEmitsOnlyResolvableKinds()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Cone\n\n## 第三章 Synthetic\n\n"
            + "**定理 3.1(Known)[证]。**known。\n\n"
            + "**猜想 3.2(Unknown)[证]。**unknown。\n");

        AssertEveryEmittedKindResolves(AtomizerRegistry.ConeId, bytes, DispositionRules);
    }

    [Fact]
    public void ObserverProducerEmitsOnlyResolvableKinds()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**Known** claim。\n\n**未登记体。** claim。\n");

        AssertEveryEmittedKindResolves(AtomizerRegistry.ObserverId, bytes, DispositionRules);
    }

    [Fact]
    public void PeriodicTreeProducerEmitsOnlyResolvableKinds()
    {
        var structured = Encoding.UTF8.GetBytes("# Registry\n\n## 1. First\n\nclaim。\n");
        var coarse = Encoding.UTF8.GetBytes("{\"row\":1}\n");

        AssertEveryEmittedKindResolves(
            AtomizerRegistry.PeriodicTreeId,
            structured,
            DispositionRules);
        AssertEveryEmittedKindResolves(
            AtomizerRegistry.PeriodicTreeId,
            coarse,
            DispositionRules);
    }

    [Fact]
    public void WmProducerEmitsOnlyResolvableKinds()
    {
        var bytes = Encoding.UTF8.GetBytes(CanonicalWmFixture());

        AssertEveryEmittedKindResolves(AtomizerRegistry.WmId, bytes, DispositionRules);
    }

    [Fact]
    public void DeclaredDialectUnregisteredGenreResolvesAndProjectsAsNotFormalizable()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n# 未登记体 1.1\n\nclaim。\n");
        var kinds = AtomizerRegistry.ResolveContentKinds("dialect:qdo", bytes, DispositionRules);
        var kind = Assert.Single(kinds).Value;

        Assert.Equal("unregistered:未登记体", kind);
        Assert.Equal(
            (DigestionContentRole.NotFormalizable, "unregistered:未登记体"),
            DigestionContentDisposition.Resolve(kind));
        var atom = Assert.Single(AtomizerRegistry.Atomize("dialect:qdo", bytes, DispositionRules).Claims);
        var entry = DigestionTestSupport.Entry(atom, "declared-unregistered", "dialect:qdo");
        var evaluation = new DigestionLedgerEvaluation(
            [new DigestionEntryEvaluation(
                entry,
                DigestionReceiptAlignment.Seen,
                atom,
                entry.ProjectedStatus,
                false,
                [])],
            []);
        var projection = DigestionFrontierTestProjection.Create(
            evaluation,
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [entry.AtomId] = kind,
            });

        var projected = Assert.Single(projection.Entries);
        Assert.Equal(DigestionFrontierDisposition.NotFormalizable, projected.PrimaryDisposition);
        Assert.Equal("unregistered:未登记体", projected.PrimaryDetail);
    }

    private static void AssertEveryEmittedKindResolves(
        string atomizerId,
        byte[] bytes,
        TheoryAtomizerRules rules)
    {
        var kinds = AtomizerRegistry.ResolveContentKinds(atomizerId, bytes, rules);

        Assert.NotEmpty(kinds);
        Assert.All(kinds.Values, static kind => _ = DigestionContentDisposition.Resolve(kind));
    }
}
