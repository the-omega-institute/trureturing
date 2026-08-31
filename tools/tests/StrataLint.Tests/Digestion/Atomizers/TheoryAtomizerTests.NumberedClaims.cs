using System.Collections.Immutable;
using System.Reflection;
using System.Security.Cryptography;
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
    public void UnknownClaimLeadsAreAllAdmittedAndReportedInTheMarker()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**甲体 1.1(A)**。一。\n\n**乙体 2.2(B)**。二。\n\n**丙体 3.3(C)**。三。\n");

        var alignment = AlignUnregisteredGenres(bytes);

        Assert.Empty(alignment.Findings);
        Assert.Equal(3, alignment.Residual.Length);
        Assert.All(alignment.Residual, static item => AssertContentIdentity(item.Atom));
        Assert.Equal(
            ["丙体", "乙体", "甲体"],
            alignment.GenreRegistryChecks["source"].UnregisteredGenres.ToArray());
        Assert.Empty(alignment.Fallbacks);
    }

    [Fact]
    public void ARepeatedUnknownLeadIsNamedOnceInTheMarker()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**甲体 1.1(A)**。一。\n\n**甲体 2.2(B)**。二。\n\n**乙体 3.3(C)**。三。\n");

        var alignment = AlignUnregisteredGenres(bytes);

        Assert.Empty(alignment.Findings);
        Assert.Equal(3, alignment.Residual.Length);
        Assert.Equal(
            ["乙体", "甲体"],
            alignment.GenreRegistryChecks["source"].UnregisteredGenres.ToArray());
        Assert.Empty(alignment.Fallbacks);
    }

    [Theory]
    [InlineData("评注 27.363–27.365")]
    [InlineData("注记 1.1–1.2")]
    public void EveryRemarkGenreOpensASectionNotOnlyTheFirstOneListed(string heading)
    {
        var bytes = Encoding.UTF8.GetBytes($"# PZG\n\n## {heading}\n\n正文。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentity(Assert.Single(document.Claims));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgThreeSegmentClaimNumbersKeepTheirThirdSegmentInTheLocator()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**注记 3.6.1(A)**。一。\n\n**注记 3.6.2(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 2);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgTwoSegmentClaimNumbersAreUnchangedByThreeSegmentSupport()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 7.15(A)**。一。\n\n**定理 7.15′(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 2);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ACandidateTheoremLeadCarriesTheSameLocatorAsItsEnrolledForm()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**候签定理 7.1′(A)**。一。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 1);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void TheLongerCandidateTheoremLeadDoesNotShadowThePlainTheoremLead()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 7.1(A)**。一。\n\n**候签定理 7.2(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 2);
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
        AssertContentIdentity(plan.Parent);
        Assert.All(plan.Children, AssertContentIdentity);
        Assert.Equal([7, 196], plan.Children.Select(static child => child.StartByte).ToArray());
        Assert.Equal([196, 379], plan.Children.Select(static child => child.EndByte).ToArray());
        Assert.Equal(
            [
                "sha256:2b465d7578add091f8bf5c03ccc921d04a2cb5a552e67f3a7e3b400e9b7adc65",
                "sha256:cb882fe434d77c8e0215d129decf54142d9bfea0f02d196007b18068aa90194b",
            ],
            plan.Children.Select(static child => child.Fingerprints.RawSha256).ToArray());
        var repeated = Assert.Single(second.ClausePlans);
        Assert.Equal(plan.Parent.Fingerprints.RawSha256, repeated.Parent.Fingerprints.RawSha256);
        Assert.Equal(
            plan.Children.Select(static child => (
                child.Fingerprints.RawSha256,
                child.StartByte,
                child.EndByte,
                child.Fingerprints.RawSha256)),
            repeated.Children.Select(static child => (
                child.Fingerprints.RawSha256,
                child.StartByte,
                child.EndByte,
                child.Fingerprints.RawSha256)));
        Assert.All(plan.Children.Zip(repeated.Children), pair =>
            Assert.Equal(pair.First.RawBytes.ToArray(), pair.Second.RawBytes.ToArray()));
    }

    [Fact]
    public void PzgClausePlanChildrenResolveThroughTheCanonicalClaimResolver()
    {
        const string secondClause = "**第二条**。第二条。\n";
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 9.10**。第一条。\n\n" + secondClause);
        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var parent = Assert.Single(document.Claims);
        var plan = Assert.Single(document.ClausePlans);
        Assert.Equal(2, plan.Children.Length);
        var child = plan.Children[1];
        var expectedBytes = Encoding.UTF8.GetBytes(secondClause);
        var expectedFingerprint = "sha256:"
            + Convert.ToHexStringLower(SHA256.HashData(expectedBytes));

        Assert.Equal(parent.Fingerprints.RawSha256, plan.Parent.Fingerprints.RawSha256);
        Assert.Equal(expectedBytes, child.RawBytes.ToArray());
        Assert.Equal(expectedFingerprint, child.Fingerprints.RawSha256);
        Assert.InRange(child.StartByte, parent.StartByte, parent.EndByte - 1);
        Assert.InRange(child.EndByte, child.StartByte + 1, parent.EndByte);
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
        Assert.Equal(35, document.Claims.Select(static atom => atom.Fingerprints.RawSha256)
            .Distinct(StringComparer.Ordinal).Count());

        var landing = ClaimContaining(document, "**引理 3.1(");
        var escape = ClaimContaining(document, "**定理 3.4(");
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
        AssertContentIdentity(registryAtom);
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
