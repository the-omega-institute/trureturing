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
                schema_version = 4
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
    public void MatchingIsUnchangedAcrossRepeatedAndCrossEntryUse(string pattern, string path, bool expected)
    {
        for (var iteration = 0; iteration < 2; iteration++)
        {
            Assert.Equal(expected, FileMapGlob.Create(pattern).IsMatch(path));
            Assert.Equal(expected, FileMapGlob.CreateForAdmissionPlane(pattern).IsMatch(path));
        }
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
