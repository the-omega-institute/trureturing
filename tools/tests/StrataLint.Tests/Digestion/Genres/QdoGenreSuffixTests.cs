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

    [Fact]
    public void Pr2096HeadTokenMultisetHasNoUnregisteredGenres()
    {
        var (bytes, expectedPaths) = Pr2096Fixture();

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        Assert.Equal(363, document.Claims.Length);
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(expectedPaths, document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void AnUnlistedCompoundEndingInExampleHeadClosesTheProductiveClass()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n## 极小反例 40.1\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        Assert.Equal("example/40.1", Assert.Single(document.Claims).AstPath);
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ExactConditionTheoremGenreWinsBeforeSuffixResolution()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n## 条件定理 40.2\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        Assert.Equal("theorem-form/40.2", Assert.Single(document.Claims).AstPath);
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void RemovingTheSuffixRuleMakesThePr2096FixtureUnregisteredAgain()
    {
        var rules = LoadRules(RemoveQdoSuffixRule(CanonicalData));
        var (bytes, _) = Pr2096Fixture();

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
            Assert.Equal($"{kind}/41.1", Assert.Single(after.Claims).AstPath);
            Assert.Empty(after.UnregisteredGenres);
            Assert.Equal(bytes, after.Reassemble().ToArray());
        }

        AssertGenreTable(LegacyGictGenres, migrated.GictGenres);
        AssertGenreTable(LegacyPzgGenres, migrated.PzgGenres);
        Assert.Equal(["qdo"], migrated.Dialects.Keys.Order(StringComparer.Ordinal));
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

        Assert.Equal(
            ["observation/1.1", "theorem/1.2"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
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

        Assert.Equal("theorem/1.1", Assert.Single(document.Claims).AstPath);
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

        Assert.Equal("observation/1.1", Assert.Single(document.Claims).AstPath);
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    private static string CanonicalData => Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);

    private static TheoryAtomizerRules LoadRules(string data) => TheoryAtomizerDataLoader.Load(
        DigestionTestSupport.Snapshot(
            (TheoryAtomizerDataLoader.DataPath, Encoding.UTF8.GetBytes(data))));

    private static void AssertGenreTable(
        IEnumerable<(string Token, string Kind)> expected,
        IEnumerable<AtomizerMapping> actual)
    {
        Assert.Equal(
            expected.OrderBy(static item => item.Token, StringComparer.Ordinal),
            actual.Select(static item => (item.Token, Kind: item.Value))
                .OrderBy(static item => item.Token, StringComparer.Ordinal));
    }

    private static (byte[] Bytes, string[] ExpectedPaths) Pr2096Fixture()
    {
        var source = new StringBuilder("# QDO\n\n");
        var paths = new List<string>(363);
        var number = 1;
        foreach (var (token, count, kind) in Pr2096TokenMultiset)
        {
            for (var occurrence = 0; occurrence < count; occurrence++)
            {
                source.Append("## ").Append(token).Append(" 40.").Append(number).Append("\n\n证。\n\n");
                paths.Add($"{kind}/40.{number}");
                number++;
            }
        }

        Assert.Equal(363, paths.Count);
        Assert.Equal(12, Pr2096TokenMultiset.Length);
        return (Encoding.UTF8.GetBytes(source.ToString()), paths.ToArray());
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
