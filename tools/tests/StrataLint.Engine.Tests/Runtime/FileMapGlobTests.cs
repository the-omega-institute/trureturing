using System.Text;

namespace StrataLint.Engine.Tests;

public sealed class FileMapGlobTests
{
    [Theory]
    [InlineData("")]
    [InlineData(" ")]
    [InlineData(" D5/*.lean")]
    [InlineData("D5/*.lean ")]
    [InlineData("../D5/*.lean")]
    [InlineData("D5/./*.lean")]
    [InlineData("/D5/**/*.lean")]
    [InlineData("D5\\*.lean")]
    [InlineData("D5//*.lean")]
    [InlineData("D5/")]
    [InlineData("D5/é.lean")]
    [InlineData("D5/\t.lean")]
    public void AdmissionPatternReuseCannotBypassStrictValidation(string pattern)
    {
        _ = FileMapGlob.CreateForAdmissionPlane(pattern);

        for (var iteration = 0; iteration < 2; iteration++)
        {
            Assert.Throws<FileMapPatternException>(() => FileMapGlob.Create(pattern));
            var manifest = Encoding.UTF8.GetBytes($$"""
                schema_version = 6
                [[files]]
                pattern = '''{{pattern}}'''
                """ + "\n");
            Assert.Throws<FileMapPatternException>(() => FileMapSymlinkPolicy.Parse(manifest, "fixture"));
        }
    }

    [Fact]
    public void NullStrictPatternStillReportsUnsafePattern() =>
        Assert.Throws<FileMapPatternException>(() => FileMapGlob.Create(null!));

    [Fact]
    public void LiteralPatternBatchUsesBoundedAllocation()
    {
        var batchId = Guid.NewGuid().ToString("N");
        var patterns = Enumerable.Range(0, 64)
            .Select(index => $"allocation/{batchId}/Literal{index:D2}[1]+(x).lean")
            .ToArray();
        var negativePaths = patterns.Select(pattern => pattern + ".extra").ToArray();
        var positiveMatches = 0;
        var negativeMatches = 0;

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var index = 0; index < patterns.Length; index++)
        {
            var glob = FileMapGlob.Create(patterns[index]);
            if (glob.IsMatch(patterns[index])) positiveMatches++;
            if (glob.IsMatch(negativePaths[index])) negativeMatches++;
        }
        var allocatedBytes = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(patterns.Length, positiveMatches);
        Assert.Equal(0, negativeMatches);
        Assert.True(allocatedBytes <= 8 * 1024 * 1024,
            $"Literal pattern construction and matching allocated {allocatedBytes} bytes; limit is 8 MiB.");
    }

    [Theory]
    [InlineData("", "x")]
    [InlineData("D5/é.lean", "D5/e.lean")]
    public void AdmissionOnlyLiteralsMatchExactly(string pattern, string otherPath)
    {
        var glob = FileMapGlob.CreateForAdmissionPlane(pattern);
        Assert.True(glob.IsMatch(pattern));
        Assert.False(glob.IsMatch(otherPath));
        Assert.Throws<FileMapPatternException>(() => FileMapGlob.Create(pattern));
    }

    [Fact]
    public void WildcardPatternBatchUsesBoundedAllocation()
    {
        var batchId = Guid.NewGuid().ToString("N");
        var prefixes = Enumerable.Range(0, 64)
            .Select(index => $"allocation/{batchId}/Item{index:D2}[1]+(x)/")
            .ToArray();
        var positiveMatches = 0;
        var negativeMatches = 0;

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var index = 0; index < prefixes.Length; index++)
        {
            var glob = FileMapGlob.Create(prefixes[index] + "**/*.lean");
            if (glob.IsMatch(prefixes[index] + "Value.lean")) positiveMatches++;
            if (glob.IsMatch(prefixes[index] + "nested/Value.lean")) positiveMatches++;
            if (glob.IsMatch(prefixes[(index + 1) % prefixes.Length] + "Value.lean")) negativeMatches++;
            if (glob.IsMatch(prefixes[index].ToUpperInvariant() + "Value.lean")) negativeMatches++;
            if (glob.IsMatch(prefixes[index] + "nested/Value.cs")) negativeMatches++;
        }
        var allocatedBytes = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(2 * prefixes.Length, positiveMatches);
        Assert.Equal(0, negativeMatches);
        Assert.True(allocatedBytes <= 8 * 1024 * 1024,
            $"Wildcard pattern construction and matching allocated {allocatedBytes} bytes; limit is 8 MiB.");
    }

    [Theory]
    [InlineData("a\n/**/*.lean", "a\n/Value.lean", true)]
    [InlineData("a\n/**/*.lean", "a\n/nested/Value.lean", true)]
    [InlineData("a\n/**/*.lean", "a\n/nested\n/Value.lean", false)]
    [InlineData("a\n/**/*.lean", "a\n/Val\nue.lean", true)]
    [InlineData("Root[1]+(x)/**/*.lean", "Root[1]+(x)/nested/Value.lean", true)]
    [InlineData("Root[1]+(x)/**/*.lean", "Root1x/nested/Value.lean", false)]
    public void AdmissionWildcardPrefixesRetainLiteralAndNewlineSemantics(
        string pattern, string path, bool expected) =>
        Assert.Equal(expected, FileMapGlob.CreateForAdmissionPlane(pattern).IsMatch(path));

    [Fact]
    public void QuestionMarkIsRejectedByBothEntriesOnEveryCall()
    {
        for (var iteration = 0; iteration < 2; iteration++)
        {
            Assert.Throws<FileMapPatternException>(() => FileMapGlob.Create("D5/?.lean"));
            Assert.Throws<FileMapPatternException>(() => FileMapGlob.CreateForAdmissionPlane("D5/?.lean"));
        }
    }

    [Theory]
    [InlineData("D5/*.lean", "D5/Result.lean", true)]
    [InlineData("D5/*.lean", "D5/S0/Result.lean", false)]
    [InlineData("D5/**/*.lean", "D5/Result.lean", true)]
    [InlineData("D5/**/*.lean", "D5/S0/Carrier/Result.lean", true)]
    [InlineData("D5/**", "D5/S0/Carrier/Result.lean", true)]
    [InlineData("D5/**", "D5/", true)]
    [InlineData("D5/*.lean", "Other/D5/Result.lean", false)]
    [InlineData("D5/*.lean", "D5/Result.lean\n", false)]
    [InlineData("D5/Result[1]+(x).lean", "D5/Result[1]+(x).lean", true)]
    [InlineData("D5/Result[1]+(x).lean", "D5/Result1x.lean", false)]
    [InlineData("D5/A.lean", "D5/A.lean", true)]
    [InlineData("D5/A.lean", "D5/a.lean", false)]
    [InlineData("D5/a.lean", "D5/a.lean", true)]
    [InlineData("D5/a.lean", "D5/A.lean", false)]
    [InlineData("D5/A.lean", "D5/A.lean.extra", false)]
    [InlineData("D5/*.lean", "D5/A.cs", false)]
    [InlineData("**/*.lean", "Result.lean", true)]
    [InlineData("**/*.lean", "D5/Result.lean", true)]
    [InlineData("*.lean", "D5/Result.lean", false)]
    public void MatchingIsUnchangedAcrossRepeatedAndCrossEntryUse(string pattern, string path, bool expected)
    {
        for (var iteration = 0; iteration < 2; iteration++)
        {
            Assert.Equal(expected, FileMapGlob.Create(pattern).IsMatch(path));
            Assert.Equal(expected, FileMapGlob.CreateForAdmissionPlane(pattern).IsMatch(path));
        }
    }

    [Theory]
    [InlineData("D5/A.lean")]
    [InlineData("D5/*.lean")]
    [InlineData("**")]
    public void NullPathsRetainTheMatcherDiagnostic(string pattern)
    {
        var strict = Assert.Throws<ArgumentNullException>(() => FileMapGlob.Create(pattern).IsMatch(null!));
        var admission = Assert.Throws<ArgumentNullException>(() => FileMapGlob.CreateForAdmissionPlane(pattern).IsMatch(null!));
        Assert.Equal("input", strict.ParamName);
        Assert.Equal("input", admission.ParamName);
    }

    [Fact]
    public void ConcurrentEntriesKeepIndependentCaseSensitiveMatches()
    {
        Parallel.For(0, 64, iteration =>
        {
            var name = iteration % 2 == 0 ? "Upper" : "upper";
            var other = iteration % 2 == 0 ? "upper" : "Upper";
            var pattern = $"concurrent/{name}/**/Value[1].cs";
            var glob = iteration % 4 < 2
                ? FileMapGlob.Create(pattern)
                : FileMapGlob.CreateForAdmissionPlane(pattern);
            Assert.True(glob.IsMatch($"concurrent/{name}/Value[1].cs"));
            Assert.True(glob.IsMatch($"concurrent/{name}/nested/Value[1].cs"));
            Assert.False(glob.IsMatch($"concurrent/{other}/Value[1].cs"));
            Assert.False(glob.IsMatch($"concurrent/{name}/Value1.cs"));
        });
    }
}
