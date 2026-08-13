using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeLegacyConstructorBudgetTests
{
    private const string PathA = "Blueprint/Test/A.scribe.cs";
    private const string PathB = "Blueprint/Test/B.scribe.cs";

    [Fact] public void RealCallIsCounted() => Assert.Equal(1, Count("DocumentBlock.Describe.Definition(x);"));
    [Fact] public void CommentLookalikesAreIgnored() => Assert.Equal(0, Count("// DocumentBlock.Describe.Definition(x)\n/* DefinitionDsl.LeanTheorem(x) */"));
    [Fact] public void OrdinaryStringLookalikesAreIgnored() => Assert.Equal(0, Count("\"DefinitionDsl.LeanTheorem(x)\";"));
    [Fact] public void VerbatimStringLookalikesAreIgnored() => Assert.Equal(0, Count("@\"DefinitionDsl.LeanTheorem(x)\";"));
    [Fact] public void RawStringLookalikesAreIgnored() => Assert.Equal(0, Count("\"\"\"DefinitionDsl.LeanTheorem(x)\"\"\";"));
    [Fact] public void InterpolatedStringLookalikesAreIgnored() => Assert.Equal(0, Count("$\"DefinitionDsl.LeanTheorem(x)\";"));

    [Fact]
    public void QualifiedAndUsingStaticCallsAreCounted()
    {
        const string text = "using static StrataLint.Scribe.DefinitionDsl; class C { void M() { DefinitionDsl.LeanTheorem(x); LeanTheorem(x); } }";
        Assert.Equal(2, Count(text));
    }

    [Fact]
    public void SameNamedUserMethodIsNotCounted() =>
        Assert.Equal(0, Count("class C { object LeanTheorem(string x) => x; void M() { LeanTheorem(x); } }"));

    [Fact]
    public void SameNameDeclarationIsNotCountedAlongsideInvocation()
    {
        const string text = "class C { object LeanTheorem(string x) => x; void M() { DefinitionDsl.LeanTheorem(x); } }";
        Assert.Equal(1, Count(text));
    }

    [Fact]
    public void NameofIsNotCounted() =>
        Assert.Equal(0, Count("class C { string M() => nameof(LeanTheorem); }"));

    [Fact] public void NewFileUsingLegacyConstructorIsRejected() => Assert.Single(Evaluate(null, "DefinitionDsl.LeanTheorem(x);"));
    [Fact] public void DeletingCallInSameFileIsAllowed() => Assert.Empty(Evaluate("DefinitionDsl.LeanTheorem(x);", ""));

    [Fact]
    public void CrossFileOffsetsAreRejected()
    {
        var fixture = Fixture(
            (PathA, "", "DefinitionDsl.LeanTheorem(x);"),
            (PathB, "DefinitionDsl.LeanTheorem(x);", ""));
        Assert.Single(Evaluate(fixture));
    }

    [Fact]
    public void ByteIdenticalRenameOfACleanFileIsAllowed()
    {
        const string text = "ScribeNode.Create(handle);";
        Assert.Empty(Evaluate(Fixture((PathA, text, null), (PathB, null, text))));
    }

    [Fact]
    public void ByteIdenticalRenameNoLongerCarriesALegacyConstructorAcross()
    {
        // While the migration ran, moving a file that still held a legacy constructor was allowed:
        // the count had not increased, and refusing the move would have blocked bucket splits.
        // The migration is finished and every Blueprint document holds zero, so the question is no
        // longer "did this file get worse" but "does this file hold one at all". A rename cannot
        // launder one back in.
        const string text = "DefinitionDsl.LeanTheorem(x);";
        Assert.Single(Evaluate(Fixture((PathA, text, null), (PathB, null, text))));
    }

    [Fact]
    public void RenameWithEditIsRejected() =>
        Assert.Single(Evaluate(Fixture((PathA, "DefinitionDsl.LeanTheorem(x);", null), (PathB, null, "DefinitionDsl.LeanTheorem(x); DefinitionDsl.LeanTheorem(y);"))));

    [Fact]
    public void AmbiguousRenameNeedsNoSpecialCaseNow()
    {
        // The rule used to pair deleted and added files by identical bytes so that a pure move kept
        // its old budget, and it failed closed when that pairing was not unique. With the budget
        // gone there is nothing to carry across, so the ambiguity has no meaning: the surviving file
        // is judged on what it holds, exactly like any other.
        const string text = "DefinitionDsl.LeanTheorem(x);";
        var findings = Evaluate(Fixture(
            (PathA, text, null),
            ("Blueprint/Test/C.scribe.cs", text, null),
            (PathB, null, text)));
        Assert.Single(findings);
        Assert.Contains(findings, finding => finding.Message.Contains("is present", StringComparison.Ordinal));
    }

    [Fact] public void NewFileUsingOnlyNewApiIsAllowed() => Assert.Empty(Evaluate(null, "ScribeNode.Create(handle);"));
    [Fact] public void DocumentEdgeDependencyIsNotManaged() => Assert.Empty(Evaluate(null, "DocumentEdge.Dependency(x);"));

    private static int Count(string text) =>
        ScribeLegacyConstructorScanner.Count(text).Values.Sum();

    private static System.Collections.Immutable.ImmutableArray<RuleFinding> Evaluate(string? baseline, string? current) =>
        Evaluate(Fixture((PathA, baseline, current)));

    private static System.Collections.Immutable.ImmutableArray<RuleFinding> Evaluate(RuleFixture fixture) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(26), fixture.BuildForProtectedRuleCompatibility()).Diagnostics
            .Select(d => new RuleFinding(d.Path, d.Message))
            .ToImmutableArray();

    private static RuleFixture Fixture(params (string Path, string? Baseline, string? Current)[] files)
    {
        var fixture = new RuleFixture();
        fixture.Changes.Clear();
        foreach (var (path, baseline, current) in files)
        {
            fixture.Baseline.Remove(path);
            fixture.Files.Remove(path);
            if (baseline is not null) fixture.Baseline[path] = baseline;
            if (current is not null) fixture.Files[path] = current;
            fixture.Changes.Add(path);
        }
        return fixture;
    }
}
