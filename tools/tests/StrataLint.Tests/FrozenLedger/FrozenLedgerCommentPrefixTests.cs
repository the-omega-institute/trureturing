using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("/-- A proposition. -/ ")]
    [InlineData("/-- A proposition. -/ noncomputable ")]
    [InlineData("/-- A proposition. -/ @[simp] ")]
    [InlineData("/- Outer /- inner -/ comment. -/ /-- A proposition. -/ ")]
    [InlineData("/-- A proposition.\nIts definition follows. -/ ")]
    public void MathlibReanchorAcceptsTopLevelCommentPrefixedDeclarations(string prefix)
    {
        var source = prefix + "def p : Prop := True\n"
            + "/-- A proof. -/ theorem a : p := by trivial\n";
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", source, statementMaterial: "old elaborated p"), Module("B")],
            candidateModules: [ModuleWithReport("A", source, statementMaterial: "new elaborated p"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("")]
    [InlineData("  ")]
    public void MathlibReanchorRejectsCommentPrefixedDefinitionWeakening(string indentation)
    {
        var baseline = indentation + "/-- A proposition. -/ def p : Prop := False\n"
            + "theorem a : p := by contradiction\n";
        var candidate = baseline.Replace("False", "True", StringComparison.Ordinal)
            .Replace("contradiction", "trivial", StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", baseline, statementMaterial: "old elaborated p"), Module("B")],
            candidateModules: [ModuleWithReport("A", candidate, statementMaterial: "new elaborated p"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorAcceptsUnchangedIndentedCommentPrefixedDeclaration()
    {
        const string source = "  /-- Hidden. -/ def p : Prop := True\n"
            + "theorem a : p := by trivial\n";
        var result = ValidateMathlibReanchor(
            baseModules: [ModuleWithReport("A", source, statementMaterial: "old elaborated p"), Module("B")],
            candidateModules: [ModuleWithReport("A", source, statementMaterial: "new elaborated p"), Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("\"/- comment -/\" theorem")]
    [InlineData("def x := 1 /- comment -/ theorem")]
    [InlineData("-- /- comment -/\n  theorem")]
    [InlineData("  /- comment\n continued -/ theorem")]
    [InlineData("/- comment -/\n  theorem")]
    public void MathlibReanchorTokenizerPreservesNonTopLevelCommentContexts(string source)
    {
        var token = Assert.Single(LeanSourceTokenizer.Tokenize(source), token => token.Text == "theorem");
        Assert.True(token.Column > 0);
        Assert.True(token.CommandColumn > 0);
    }

    [Fact]
    public void MathlibReanchorTokenizerRejectsUnterminatedCommentPrefix() =>
        Assert.Throws<LeanSourceExtractionException>(() => LeanSourceTokenizer.Tokenize("/-- unclosed theorem"));

}
