namespace StrataLint.Scribe.Tests;

public sealed class ChannelMonotoneDocumentTests
{
    [Fact]
    public void ChannelMonotonicityStatesTheRestatementAndItsHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/ChannelMonotone");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/ChannelMonotone.kl_divergence_channel_le",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\operatorname{Fintype}(X)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\operatorname{Nonempty}(X)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\operatorname{Fintype}(Y)", latex, StringComparison.Ordinal);
        Assert.DoesNotContain(@"\operatorname{Nonempty}(Y)", latex, StringComparison.Ordinal);
        Assert.Contains(@"0<p(x)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{x}p(x)=1", latex, StringComparison.Ordinal);
        Assert.Contains(@"0<q(x)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{x}q(x)=1", latex, StringComparison.Ordinal);
        Assert.Contains(@"0<W(x, y)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{y}W(x, y)=1", latex, StringComparison.Ordinal);
        Assert.Contains(
            @"D(Wp\Vert\Vert Wq) \le D(p\Vert\Vert q)",
            latex,
            StringComparison.Ordinal);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "strictly positive normalized real mass functions",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("strictly positive stochastic kernel", prose, StringComparison.Ordinal);
        Assert.Contains("every row sums to one", prose, StringComparison.Ordinal);
        Assert.Contains(
            "exactly the hypotheses required by D5/S3/Divergence/DpiDefect.dpi_defect_nonneg; nothing beyond them is assumed",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This module restates D5/S3/Divergence/DpiDefect.dpi_defect_nonneg in inequality form",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The proof of the mathematical content lives in DpiDefect",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "ChannelMonotone only converts its nonnegative defect conclusion into the equivalent output-at-most-input inequality",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This module is a redundant re-proof: the same proposition was already frozen as D5/S3/Divergence/DpiDefect.dpi_defect_nonneg before this module was deposited.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The theorem remains true and machine-verified; the redundancy lies in this module, not in the mathematics.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It is retained, rather than removed, only because the frozen ledger currently has no revoke writer (issue #1030); removal is the resolution that CLAUDE.md 第6条 would require.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Therefore, this module is a documented compromise and does not by itself satisfy 唯一真源 / single source of truth.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Readers and downstream work should depend on D5/S3/Divergence/DpiDefect.dpi_defect_nonneg, not on this module.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "data-processing inequality that wave 11's D5/S3/Divergence/MarginalMonotone module explicitly did not claim",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "first-coordinate marginalization is the special case of forgetting a coordinate",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "finite real-valued klDivergence of ClassicalDPI",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "repository's single source for the definition",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("not a measure-theoretic divergence", prose, StringComparison.Ordinal);
        Assert.Contains(
            "InformationTheory.klDiv_compProd_eq_add is not used",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "no ENNReal/finite-sum bridge is established here",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "strict positivity of the kernel and of both input distributions is required",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Channels with zero transition probabilities and distributions with zero mass are outside this module's scope",
            prose,
            StringComparison.Ordinal);
    }
}
