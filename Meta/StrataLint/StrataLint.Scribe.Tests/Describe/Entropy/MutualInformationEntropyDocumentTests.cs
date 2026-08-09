namespace StrataLint.Scribe.Tests;

public sealed class MutualInformationEntropyDocumentTests
{
    [Fact]
    public void MutualInformationEntropyStatesTheGeneralPinAndDerivedSubadditivity()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/MutualInformationEntropy");
        var describes = definition.Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(2, describes.Length);
        Assert.Equal(
            "D5/S3/Entropy/MutualInformationEntropy.mutual_information_eq_entropy_sub",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describes[0].Statement).Value.Value);
        Assert.Equal(
            "D5/S3/Entropy/MutualInformationEntropy.entropy_subadditive",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describes[1].Statement).Value.Value);
        Assert.All(
            describes,
            static describe =>
                Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind));

        var decomposition = LatexWriter.WriteStatement(
            describes[0].StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\" +
            @"(\forall i, j, 0\le p(i,j)) \Rightarrow\\" +
            @"\operatorname{mutualInformation}(p)=" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}(p))+" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}((j,i)\mapsto p(i,j)))-" +
            @"\operatorname{shannonEntropy}(p).\end{gathered}$$",
            decomposition);

        var subadditivity = LatexWriter.WriteStatement(
            describes[1].StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\" +
            @"((\forall i, j, 0\le p(i,j)) \land \sum_{i,j}p(i,j)=1) \Rightarrow\\" +
            @"\operatorname{shannonEntropy}(p)\le" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}(p))+" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}((j,i)\mapsto p(i,j)))." +
            @"\end{gathered}$$",
            subadditivity);

        var prose = string.Join(
            " ",
            describes.SelectMany(static describe => describe.Content.Items)
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "The decomposition is the identity tying this bucket's two definitions together: mutual information equals the sum of the two marginal entropies minus the joint entropy.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The units are nats because the definitions use Real.log.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("This theorem is the general pin.", prose, StringComparison.Ordinal);
        Assert.Contains(
            "The sibling module D5/S3/Entropy/MutualInformationProduct constrains the mutual-information definition only on product joints, and is blind to a reference that agrees there but differs on correlated joints.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The decomposition holds for every admissible joint, including correlated joints, so it constrains the definition exactly where the product-law identity could not.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It does not by itself make the mutual-information definition beyond question; it establishes this specific consistency relation with the imported entropy and marginal definitions.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The hypotheses are deliberately minimal: the decomposition needs only nonnegativity of the joint, and normalization is not required.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This asymmetry matters because a reader may expect both results to require a probability distribution.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Zero-mass cells are handled by cases without assuming positive marginals.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "In particular, a cell may vanish while both of its marginals are positive; that case is covered, not excluded.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Entropy subadditivity is derived, not independently proven.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The proof rewrites the decomposition against the frozen mutual_information_nonneg theorem; nothing about nonnegativity is re-proved.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Normalization enters only here, because it is required to invoke that frozen nonnegativity theorem.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It does not give an equality condition for subadditivity: no characterization of when H(X,Y) = H(X) + H(Y), equivalently independence, is claimed.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It says nothing about conditional entropy or conditional mutual information, and nothing beyond two coordinates.",
            prose,
            StringComparison.Ordinal);
    }
}
