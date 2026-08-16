using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    public static TheoryData<string> PrefixMatchedTables => new()
    {
        nameof(TheoryAtomizerRules.ObserverClaimPrefixes),
        nameof(TheoryAtomizerRules.GictClaimPrefixes),
        nameof(TheoryAtomizerRules.PzgHeadingPrefixes),
    };

    [Theory]
    [MemberData(nameof(PrefixMatchedTables))]
    public void NoPrefixMatchedEntryIsSwallowedByAShorterOne(string table)
    {
        // These tables are consumed with FirstOrDefault(text.StartsWith(token)) but are
        // ordered ordinally, not longest-first, so an entry that starts with another entry
        // can never be reached: the shorter one always matches first. Nothing in the volume
        // dialects trips this today; the assertion exists because the same shape — taking a
        // representative out of an ordered table — silently dropped PZG_BEDC's
        // remark/27.363-27.365 section atoms when 注记 was registered ahead of 评注.
        var tokens = typeof(TheoryAtomizerRules)
            .GetProperty(table, BindingFlags.NonPublic | BindingFlags.Instance)!
            .GetValue(DigestionTestSupport.Rules) is ImmutableArray<AtomizerMapping> mappings
            ? mappings.Select(static mapping => mapping.Token).ToArray()
            : throw new InvalidOperationException($"{table} is not a mapping table");

        var swallowed = tokens
            .SelectMany(shorter => tokens
                .Where(longer => longer != shorter
                    && longer.StartsWith(shorter, StringComparison.Ordinal))
                .Select(longer => $"{shorter} swallows {longer}"))
            .ToArray();

        Assert.Empty(swallowed);
        Assert.NotEmpty(tokens);
    }

    [Fact]
    public void UnknownClaimLeadsAreReportedAllAtOnceNotOneRunPerLead()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**甲体 1.1(A)**。一。\n\n**乙体 2.2(B)**。二。\n\n**丙体 3.3(C)**。三。\n");

        var alignment = AlignUnregisteredGenres(bytes);

        Assert.Equal(
            "source source uses claim genres its dialect does not register: 丙体, 乙体, 甲体. "
            + $"Register them in {TheoryAtomizerDataLoader.DataPath} or correct the volume.",
            Assert.Single(alignment.Findings));
        Assert.Empty(alignment.Residual);
        Assert.Empty(alignment.Fallbacks);
    }

    [Fact]
    public void ARepeatedUnknownLeadIsNamedOnceInTheSingleFinding()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**甲体 1.1(A)**。一。\n\n**甲体 2.2(B)**。二。\n\n**乙体 3.3(C)**。三。\n");

        var alignment = AlignUnregisteredGenres(bytes);

        Assert.Equal(
            "source source uses claim genres its dialect does not register: 乙体, 甲体. "
            + $"Register them in {TheoryAtomizerDataLoader.DataPath} or correct the volume.",
            Assert.Single(alignment.Findings));
        Assert.Empty(alignment.Residual);
        Assert.Empty(alignment.Fallbacks);
    }

    [Theory]
    [InlineData("评注 27.363–27.365", "remark/27.363-27.365")]
    [InlineData("注记 1.1–1.2", "remark/1.1-1.2")]
    public void EveryRemarkGenreOpensASectionNotOnlyTheFirstOneListed(
        string heading,
        string expectedAstPath)
    {
        var bytes = Encoding.UTF8.GetBytes($"# PZG\n\n## {heading}\n\n正文。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(expectedAstPath, Assert.Single(document.Claims).AstPath);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgThreeSegmentClaimNumbersKeepTheirThirdSegmentInTheLocator()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**注记 3.6.1(A)**。一。\n\n**注记 3.6.2(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            ["remark/3.6.1", "remark/3.6.2"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgTwoSegmentClaimNumbersAreUnchangedByThreeSegmentSupport()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 7.15(A)**。一。\n\n**定理 7.15′(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            ["theorem/7.15", "theorem/7.15′"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ACandidateTheoremLeadCarriesTheSameLocatorAsItsEnrolledForm()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**候签定理 7.1′(A)**。一。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            ["theorem/7.1′"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void TheLongerCandidateTheoremLeadDoesNotShadowThePlainTheoremLead()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 7.1(A)**。一。\n\n**候签定理 7.2(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            ["theorem/7.1", "theorem/7.2"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgClausePlanIsDeterministicForRealResidualTheorem18_7()
    {
        const string claim =
            "**定理 18.7(时间之矢)**〔closed〕。u_t ≠ 0 ⇒ **L(a_{t+1}) > L(a_t)**:长度沿正生成严格单调。\n"
            + "\n"
            + "*证明*。L(a_{t+1}) − L(a_t) = L(u_t) = Σ u_{t,p} log p > 0。∎\n"
            + "\n"
            + "**推论:时间方向来自素数账本增长**;只要未引入逆账本,素数生成动力学单向。"
            + "逆向运动(负指数)属群化扩张,须显式逆账本并入账(账 O-8)。\n"
            + "\n";
        var bytes = Encoding.UTF8.GetBytes("# PZG\n\n" + claim);

        var first = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var second = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        var plan = Assert.Single(first.ClausePlans);
        Assert.Equal("theorem/18.7", plan.ParentAstPath);
        Assert.Equal(
            ["theorem/18.7/clause/1", "theorem/18.7/clause/2"],
            plan.Children.Select(static child => child.AstPath).ToArray());
        Assert.Equal([7, 196], plan.Children.Select(static child => child.StartByte).ToArray());
        Assert.Equal([196, 379], plan.Children.Select(static child => child.EndByte).ToArray());
        Assert.Equal(
            [
                "sha256:2b465d7578add091f8bf5c03ccc921d04a2cb5a552e67f3a7e3b400e9b7adc65",
                "sha256:cb882fe434d77c8e0215d129decf54142d9bfea0f02d196007b18068aa90194b",
            ],
            plan.Children.Select(static child => child.Fingerprints.RawSha256).ToArray());
        var repeated = Assert.Single(second.ClausePlans);
        Assert.Equal(plan.ParentAstPath, repeated.ParentAstPath);
        Assert.Equal(
            plan.Children.Select(static child => (
                child.AstPath,
                child.StartByte,
                child.EndByte,
                child.Fingerprints.RawSha256)),
            repeated.Children.Select(static child => (
                child.AstPath,
                child.StartByte,
                child.EndByte,
                child.Fingerprints.RawSha256)));
        Assert.All(plan.Children.Zip(repeated.Children), pair =>
            Assert.Equal(pair.First.RawBytes.ToArray(), pair.Second.RawBytes.ToArray()));
    }

    [Fact]
    public void PzgClausePlanChildrenResolveThroughTheCanonicalClaimResolver()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 9.10**。第一条。\n\n**第二条**。第二条。\n");
        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var child = Assert.Single(document.ClausePlans).Children[1];

        var resolved = document.ResolveClaim(child.AstPath);

        Assert.Same(child, resolved);
    }

    [Fact]
    public void ProductionSourcesHaveStableAtomizationClassificationsAndFingerprints()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, FourthProductionSource));

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.PzgId,
            bytes,
            DigestionTestSupport.Rules);

        Assert.Equal(37, document.Claims.Length);
        Assert.Equal(
            [
                ("corollary", 2),
                ("definition", 5),
                ("example", 1),
                ("lemma", 2),
                ("observation", 3),
                ("proposition", 3),
                ("remark", 8),
                ("theorem", 13),
            ],
            document.Claims
                .GroupBy(static atom => atom.AstPath.Split('/')[0], StringComparer.Ordinal)
                .Select(static group => (Kind: group.Key, Count: group.Count()))
                .OrderBy(static item => item.Kind, StringComparer.Ordinal));

        var landing = document.ResolveClaim("lemma/3.1");
        var escape = document.ResolveClaim("theorem/3.4");
        Assert.Equal(
            "sha256:9d52e41b062f81b1ce93cf241bf4ef9806f6e6de3fe9d6d10b5dc2de6d1f929a",
            landing.Fingerprints.RawSha256);
        Assert.Equal(
            "sha256:c0a63f4cbbe848e456ae1f847150de6bf63e59a5295bf711230af4bbb4860cab",
            escape.Fingerprints.RawSha256);
        Assert.Contains("*证明。*", Encoding.UTF8.GetString(landing.RawBytes.AsSpan()), StringComparison.Ordinal);
        Assert.Contains("*证明。*", Encoding.UTF8.GetString(escape.RawBytes.AsSpan()), StringComparison.Ordinal);
        Assert.DoesNotContain("隐藏独立性", Encoding.UTF8.GetString(escape.RawBytes.AsSpan()), StringComparison.Ordinal);

        const string sourceId = "periodic-tree-registry";
        const string sourcePath = "docs/develop/theory/PERIODIC_TREE_registry.jsonl";
        var sourceRoot = $"{BackfillInventoryLoader.RootPath}{sourceId}/";
        var sourceBytes = File.ReadAllBytes(Path.Combine(root, sourcePath));
        var casPath = DigestionCasStore.RootPath
            + DigestionFingerprint.ComputeOpaque(sourceBytes).RawSha256["sha256:".Length..];
        var relativePaths = Directory
            .EnumerateFiles(Path.Combine(root, sourceRoot), "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/'))
            .Append(sourcePath)
            .Append(TheoryAtomizerDataLoader.DataPath)
            .Append(BackfillInventoryLoader.TicketIndexPath)
            .Append(casPath)
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        var raw = RawRepositorySnapshot.Create(relativePaths.Select(path => new RawRepositoryEntry(
            path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))))));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var source = Assert.Single(BackfillInventoryLoader.Load(snapshot).RequireDigestionSources());
        Assert.Equal(AtomizerRegistry.PeriodicTreeId, source.Atomizer);
        Assert.True(AtomizerRegistry.IsRegistered(source.Atomizer));
        var registryDocument = AtomizerRegistry.Atomize(
            source.Atomizer,
            sourceBytes,
            DigestionTestSupport.Rules);
        var registryAtom = Assert.Single(registryDocument.Claims);
        Assert.Equal("coarse/source", registryAtom.AstPath);
        Assert.Equal(DigestionFingerprint.ComputeOpaque(sourceBytes), registryAtom.Fingerprints);
        Assert.Equal(sourceBytes, registryAtom.RawBytes.ToArray());
        Assert.Equal(sourceBytes, registryDocument.Reassemble().ToArray());
        var environment = new ProductionCliEnvironment(
            root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null),
            new FakeLeanReportSource(LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport>(StringComparer.Ordinal))),
            new FakeScribeEmissionVerifier(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["digest-status", "--formalize-candidates"],
            environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.DoesNotContain(
            "atomizer recognition is incomplete or empty",
            console.Output,
            StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }
}
