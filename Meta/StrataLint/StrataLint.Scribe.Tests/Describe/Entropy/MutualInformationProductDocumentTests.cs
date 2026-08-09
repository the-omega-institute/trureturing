namespace StrataLint.Scribe.Tests;

public sealed class MutualInformationProductDocumentTests
{
    [Fact]
    public void MutualInformationProductStatesTheIndependencePinAndItsResidualBoundary()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/MutualInformationProduct");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Entropy/MutualInformationProduct.mutual_information_product_eq_zero",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall a: \iota\to \mathbb{R}, " +
            @"b: \kappa\to \mathbb{R},\\" +
            @"((\forall i, 0\le a(i)) \land \sum_{i}a(i)=1) \land\\" +
            @"((\forall j, 0\le b(j)) \land \sum_{j}b(j)=1) \Rightarrow\\" +
            @"\operatorname{mutualInformation}((i,j)\mapsto a(i)b(j))=0.\end{gathered}$$",
            latex);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "The theorem states that mutual information vanishes on a product joint, the independent case.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The factors a and b need only be nonnegative and normalized; no strict positivity is assumed.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Zero-mass cells are permitted, and their terms vanish.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The units are nats, consistent with the bucket's other entropy modules.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This module defines nothing; it uses the imported mutualInformation and marginal definitions.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This identity is a definition pin, not merely another consequence of divergence nonnegativity.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The nonnegativity theorem holds for any reference that is nonnegative, normalized, and absolutely continuous, so it does not certify that mutualInformation uses the product of the joint's own marginals.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "By forcing the imported definition to reduce to zero on normalized product joints, this theorem constrains the reference itself, in particular the coordinate swap used to obtain the second marginal.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The proof names the swapped second marginal explicitly as hswapped_second_marginal rather than collapsing the mutualInformation definition immediately, so the swap-specific content is present in the proof.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "A corrupted reference that reuses the first marginal for both coordinates can typecheck when the index types coincide.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "On the positive Bool example a = (3/4, 1/4) and b = (1/4, 3/4), that reference remains nonnegative, normalized, and absolutely continuous, so it survives the nonnegativity theorem, but it gives one half of log 3 instead of zero.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The product identity rejects that corruption.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The residual limitation is plain: this identity tests the reference only on product joints.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It is blind to any reference that agrees with the product of the marginals on independent joints but differs on correlated ones.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Correlated joints are exactly where mutual information does its work.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This confirms the reduction to independence at the boundary; it does not verify the reference on correlated joints.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Accordingly, the mutualInformation definition is not fully attested by this theorem.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("This is one direction only.", prose, StringComparison.Ordinal);
        Assert.Contains(
            "It does not prove the converse that vanishing mutual information forces the joint to be a product, equivalently independence.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "That converse would require the equality case of the divergence bound, and it is not established here.",
            prose,
            StringComparison.Ordinal);
    }
}
