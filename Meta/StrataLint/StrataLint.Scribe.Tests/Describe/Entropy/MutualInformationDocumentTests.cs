namespace StrataLint.Scribe.Tests;

public sealed class MutualInformationDocumentTests
{
    [Fact]
    public void MutualInformationStatesNonnegativityAndItsHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/MutualInformation");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Entropy/MutualInformation.mutual_information_nonneg",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\" +
            @"((\forall i, j, 0\le p(i,j)) \land \sum_{i,j}p(i,j)=1) \Rightarrow\\" +
            @"0\le \operatorname{mutualInformation}(p).\end{gathered}$$",
            latex);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "Mutual information is the divergence of the joint distribution from the product of its own two marginals.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The marginal definition from D5/S3/Divergence/ChainRule is deliberately reused for both coordinates: the first directly, and the second by evaluating that same marginal on the swapped joint fun r => p (r.2, r.1), so no second marginal is defined.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This reuse is deliberate: marginal remains the single source of truth.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The bound is D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg applied to the product reference; all three of its premises are discharged here, not assumed.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The product of marginals is nonnegative because each marginal is a finite sum of nonnegative joint masses.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The product reference is normalized: each marginal sum collapses to the joint sum, and the product of the two unit sums is one.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It is absolutely continuous because each joint mass is bounded by each of its marginals, so a vanishing product forces a vanishing joint mass.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Nothing about nonnegativity of divergence is re-proved.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The nonnegativity bound holds for any admissible reference and therefore does not by itself certify that the reference is the product of the joint's own marginals.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The mutual-information content resides entirely in the definition, which is where a reader should look.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Concretely, the reference at (i, j) is the first marginal at i times the second marginal at j, and the second marginal is obtained by evaluating the same marginal function on the coordinate-swapped joint fun r => p (r.2, r.1); a reader must not misread this as a second copy of the first marginal.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The hypotheses are nonnegativity and normalization of the joint only, not strict positivity.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("Zero-mass cells are permitted.", prose, StringComparison.Ordinal);
        Assert.Contains(
            "The units are nats, consistent with klDivergence and with the bucket's entropy definition.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This module proves nonnegativity only; it does not characterize the equality case that I = 0 exactly when the joint equals the product of its marginals, equivalently independence.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It does not relate mutual information to Shannon entropy: no I = H(X) + H(Y) - H(X,Y) identity is established here.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It says nothing about conditional mutual information or about more than two coordinates.",
            prose,
            StringComparison.Ordinal);
    }
}
