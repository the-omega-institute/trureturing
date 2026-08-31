using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class QdoGenreSuffixTests
{
    private const string QdoSuffixRule = """
        [[dialect.genre_suffix]]
        dialect = "qdo"
        suffix = "例"
        """;

    private static readonly (string Token, int Count, string Kind)[] Pr2096TokenMultiset =
    [
        ("定理", 205, "theorem"),
        ("定义", 75, "definition"),
        ("推论", 43, "corollary"),
        ("原理", 12, "principle"),
        ("命题", 11, "proposition"),
        ("例", 8, "example"),
        ("条件定理", 3, "theorem-form"),
        ("算法", 2, "algorithm"),
        ("猜想", 1, "observation"),
        ("特例", 1, "example"),
        ("反例", 1, "example"),
        ("关键反例", 1, "example"),
    ];

    private static void AssertContentIdentity(DigestionAtom atom) => Assert.Equal(
        DigestionFingerprint.Compute(atom.RawBytes.AsSpan()).RawSha256,
        atom.Fingerprints.RawSha256);

    [Fact]
    public void Pr2096HeadTokenMultisetHasNoUnregisteredGenres()
    {
        var bytes = Pr2096Fixture();

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        Assert.Equal(363, document.Claims.Length);
        Assert.Empty(document.UnregisteredGenres);
        Assert.All(document.Claims, AssertContentIdentity);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void Pr2096FixtureIngestsAll363ClaimsIntoAnEmptyLedger()
    {
        var bytes = Pr2096Fixture();
        var ledger = DigestionTestSupport.EmptyDocument("dialect:qdo");

        var plan = DigestionIngestor.Plan(
            ledger,
            DigestionTestSupport.Snapshot(("docs/source.md", bytes)),
            ledger);

        var source = Assert.Single(plan.Document.RequireDigestionSources());
        Assert.Equal(363, plan.ResidualOpenAdded);
        Assert.Equal(363, source.Entries.Length);
        Assert.Equal(363, plan.CasObjects.Length);
        Assert.Empty(plan.Fallbacks);
        Assert.Empty(source.GenreRegistryCheck.UnregisteredGenres);
        Assert.All(source.Entries, static entry => Assert.Equal(
            entry.Fingerprints.RawSha256["sha256:".Length..],
            entry.AtomId));
    }

    [Fact]
    public void AnUnlistedCompoundEndingInExampleHeadClosesTheProductiveClass()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n## 极小反例 40.1\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        AssertContentIdentity(Assert.Single(document.Claims));
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ExactConditionTheoremGenreWinsBeforeSuffixResolution()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n## 条件定理 40.2\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        AssertContentIdentity(Assert.Single(document.Claims));
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void RemovingTheSuffixRuleMakesThePr2096FixtureUnregisteredAgain()
    {
        var rules = LoadRules(RemoveQdoSuffixRule(CanonicalData));
        var bytes = Pr2096Fixture();

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, rules);

        Assert.Equal(["关键反例", "反例", "特例"], document.UnregisteredGenres.ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void MigrationPreservesEveryPreviouslyAcceptedLocatorAndUntouchedTable()
    {
        var migrated = LoadRules(CanonicalData);

        foreach (var (token, kind) in LegacyQdoGenres)
        {
            var bytes = Encoding.UTF8.GetBytes($"# QDO\n\n## {token} 41.1\n\n证。\n");
            var after = AtomizerRegistry.Atomize("dialect:qdo", bytes, migrated);
            AssertContentIdentity(Assert.Single(after.Claims));
            Assert.Empty(after.UnregisteredGenres);
            Assert.Equal(bytes, after.Reassemble().ToArray());
        }

        AssertLegacyTables(migrated);
    }

    [Fact]
    public void ConservativityOracleAdmitsAMonotoneGenreAddition()
    {
        // The oracle freezes legacy behaviour, not the future catalogue: adding a genre that
        // conflicts with no legacy mapping is a conservative extension and must stay green,
        // otherwise every new token would have to edit this test.
        var extended = InsertBefore(
            CanonicalData,
            "[[pzg.markers]]",
            """
            [[pzg.genres]]
            token = "增补观察"
            kind = "observation"


            """);
        var migrated = LoadRules(extended);

        AssertLegacyTables(migrated);
        Assert.Contains(
            migrated.PzgGenres,
            item => item.Token == "增补观察" && item.Value == "observation");
    }

    [Fact]
    public void ConservativityOracleAdmitsASecondDeclaredDialect()
    {
        // Declaring another dialect leaves every legacy mapping intact, so the oracle must
        // admit it; pinning the key set to exactly qdo would freeze the future catalogue.
        var extended = InsertBefore(CanonicalData, "[[dialect.genre]]", LongestDialect + "\n\n");
        var migrated = LoadRules(extended);

        AssertLegacyTables(migrated);
        Assert.Contains(LongestDialectId, migrated.Dialects.Keys);
    }

    [Fact]
    public void ConservativityOracleRejectsARewrittenLegacyMapping()
    {
        // Rewrite one legacy mapping in memory: the oracle's discriminating power is a property
        // of the predicate, not of the canonical file's byte layout, so this must not depend on
        // matching TOML text.
        var (token, kind) = LegacyPzgGenres[0];
        var rewritten = LoadRules(CanonicalData).PzgGenres
            .Select(item => item.Token == token
                ? new AtomizerMapping(item.Token, kind == "observation" ? "note" : "observation")
                : item)
            .ToArray();

        Assert.Single(rewritten, item => item.Token == token && item.Value != kind);
        Assert.Throws<Xunit.Sdk.ContainsException>(
            () => AssertGenreTable(LegacyPzgGenres, rewritten));
    }

    [Fact]
    public void ConservativityOracleRejectsADroppedLegacyMapping()
    {
        var (token, _) = LegacyPzgGenres[0];
        var dropped = LoadRules(CanonicalData).PzgGenres
            .Where(item => item.Token != token)
            .ToArray();

        Assert.Throws<Xunit.Sdk.ContainsException>(
            () => AssertGenreTable(LegacyPzgGenres, dropped));
    }

    [Fact]
    public void OverlappingSyntheticSuffixesResolveLongestFirst()
    {
        var data = InsertBefore(CanonicalData, "[[dialect.genre]]", LongestDialect + "\n\n");
        data = InsertBefore(data, "[[dialect.genre_suffix]]", LongestExactGenres + "\n\n");
        data = data.TrimEnd('\n') + "\n\n" + LongestSuffixes + "\n";
        var rules = LoadRules(data);
        var bytes = Encoding.UTF8.GetBytes("# Probe\n\n## 极新体 1.1\n\n证。\n\n## 极体 1.2\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:longest-probe", bytes, rules);

        Assert.Equal(2, document.Claims.Length);
        Assert.All(document.Claims, AssertContentIdentity);
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ExactOverrideOfLongestSuffixIsNotRejectedAsRedundant()
    {
        var exactGenres = LongestExactGenres + "\n\n" + """
            [[dialect.genre]]
            dialect = "longest-probe"
            token = "极新体"
            kind = "theorem"
            """;
        var data = InsertBefore(CanonicalData, "[[dialect.genre]]", LongestDialect + "\n\n");
        data = InsertBefore(data, "[[dialect.genre_suffix]]", exactGenres + "\n\n");
        data = data.TrimEnd('\n') + "\n\n" + LongestSuffixes + "\n";

        var rules = LoadRules(data);
        var bytes = Encoding.UTF8.GetBytes("# Probe\n\n## 极新体 1.1\n\n证。\n");
        var document = AtomizerRegistry.Atomize("dialect:longest-probe", bytes, rules);

        AssertContentIdentity(Assert.Single(document.Claims));
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void CompoundExactGenreWinsBeforeMatchingSuffix()
    {
        var data = InsertBefore(CanonicalData, "[[dialect.genre]]", ExactPriorityDialect + "\n\n");
        data = InsertBefore(data, "[[dialect.genre_suffix]]", ExactPriorityGenres + "\n\n");
        data = data.TrimEnd('\n') + "\n\n" + ExactPrioritySuffix + "\n";
        var rules = LoadRules(data);
        var bytes = Encoding.UTF8.GetBytes("# Probe\n\n## 特殊体 1.1\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:exact-priority-probe", bytes, rules);

        AssertContentIdentity(Assert.Single(document.Claims));
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    private static string CanonicalData => Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);

    private static TheoryAtomizerRules LoadRules(string data) => TheoryAtomizerDataLoader.Load(
        DigestionTestSupport.Snapshot(
            (TheoryAtomizerDataLoader.DataPath, Encoding.UTF8.GetBytes(data))));

    /// <summary>
    /// The whole legacy surface this branch must preserve. Every conservativity fixture calls
    /// it, so a reverted inclusion assertion is pinned by the monotone-extension cases.
    /// </summary>
    private static void AssertLegacyTables(TheoryAtomizerRules migrated)
    {
        AssertGenreTable(LegacyGictGenres, migrated.GictGenres);
        AssertGenreTable(LegacyPzgGenres, migrated.PzgGenres);
        Assert.Contains("qdo", migrated.Dialects.Keys);
    }

    /// <summary>
    /// Conservative extension is inclusion, not equality: every legacy mapping must still be
    /// present with its old kind. Asserting set equality would freeze the future catalogue and
    /// turn this oracle into a second copy of the canonical data, so registering any new genre
    /// would have to edit this test.
    /// </summary>
    private static void AssertGenreTable(
        IEnumerable<(string Token, string Kind)> expected,
        IEnumerable<AtomizerMapping> actual)
    {
        var current = actual.ToArray();
        foreach (var (token, kind) in expected)
        {
            Assert.Contains(current, item => item.Token == token && item.Value == kind);
        }
    }

    private static byte[] Pr2096Fixture()
    {
        var source = new StringBuilder("# QDO\n\n");
        var number = 1;
        foreach (var (token, count, _) in Pr2096TokenMultiset)
        {
            for (var occurrence = 0; occurrence < count; occurrence++)
            {
                source.Append("## ").Append(token).Append(" 40.").Append(number).Append("\n\n证。\n\n");
                number++;
            }
        }

        Assert.Equal(364, number);
        Assert.Equal(12, Pr2096TokenMultiset.Length);
        return Encoding.UTF8.GetBytes(source.ToString());
    }

    private static string RemoveQdoSuffixRule(string data) => data.Replace(
        "\n\n" + QdoSuffixRule + "\n",
        "\n",
        StringComparison.Ordinal);

    private static string InsertBefore(string data, string marker, string insertion)
    {
        var index = data.IndexOf(marker, StringComparison.Ordinal);
        Assert.True(index >= 0, $"marker not found: {marker}");
        return data.Insert(index, insertion);
    }

    private static readonly (string Token, string Kind)[] LegacyQdoGenres =
    [
        ("定理", "theorem"),
        ("定义", "definition"),
        ("命题", "proposition"),
        ("推论", "corollary"),
        ("例", "example"),
        ("算法", "algorithm"),
        ("关键反例", "example"),
        ("原理", "principle"),
        ("特例", "example"),
        ("条件定理", "theorem-form"),
        ("猜想", "observation"),
    ];

    private static readonly (string Token, string Kind)[] LegacyGictGenres =
    [
        ("勘察", "survey"),
        ("命题", "proposition"),
        ("定义", "definition"),
        ("定理", "theorem"),
        ("引理", "lemma"),
        ("推论", "corollary"),
        ("注", "note"),
        ("观察", "observation"),
    ];

    private static readonly (string Token, string Kind)[] LegacyPzgGenres =
    [
        ("复审降级注", "ledger"),
        ("候签定理", "theorem"),
        ("前沿引注", "frontier-note"),
        ("勘误正案", "ledger"),
        ("负向证据", "observation"),
        ("勘正注", "ledger"),
        ("勘误注", "ledger"),
        ("定理形", "theorem-form"),
        ("事实", "note"),
        ("公理", "axiom"),
        ("判据", "criterion"),
        ("原则", "principle"),
        ("后果", "consequence"),
        ("命题", "proposition"),
        ("契约", "contract"),
        ("定义", "definition"),
        ("定理", "theorem"),
        ("延表", "extension-table"),
        ("引理", "lemma"),
        ("推论", "corollary"),
        ("条目", "entry"),
        ("案卷", "ledger"),
        ("注记", "remark"),
        ("猜想", "observation"),
        ("约定", "specification"),
        ("范例", "example"),
        ("观察", "observation"),
        ("规格", "specification"),
        ("设置", "specification"),
        ("评注", "remark"),
        ("账目", "ledger"),
        ("路线", "route"),
        ("例", "example"),
        ("注", "remark"),
        ("窗", "observation"),
        ("系", "corollary"),
    ];

    private const string LongestDialectId = "longest-probe";

    private const string LongestDialect = """
        [[dialect]]
        id = "longest-probe"
        claim = "^(?<kind>\\p{L}+)\\s+(?<number>[0-9]+(?:\\.[0-9]+)+)"
        target = "heading"
        """;

    private const string LongestExactGenres = """
        [[dialect.genre]]
        dialect = "longest-probe"
        token = "体"
        kind = "theorem"

        [[dialect.genre]]
        dialect = "longest-probe"
        token = "新体"
        kind = "observation"
        """;

    private const string LongestSuffixes = """
        [[dialect.genre_suffix]]
        dialect = "longest-probe"
        suffix = "体"

        [[dialect.genre_suffix]]
        dialect = "longest-probe"
        suffix = "新体"
        """;

    private const string ExactPriorityDialect = """
        [[dialect]]
        id = "exact-priority-probe"
        claim = "^(?<kind>\\p{L}+)\\s+(?<number>[0-9]+(?:\\.[0-9]+)+)"
        target = "heading"
        """;

    private const string ExactPriorityGenres = """
        [[dialect.genre]]
        dialect = "exact-priority-probe"
        token = "体"
        kind = "theorem"

        [[dialect.genre]]
        dialect = "exact-priority-probe"
        token = "特殊体"
        kind = "observation"
        """;

    private const string ExactPrioritySuffix = """
        [[dialect.genre_suffix]]
        dialect = "exact-priority-probe"
        suffix = "体"
        """;
}
