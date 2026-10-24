using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HypergeometricShiftTuran;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gamma product ratios and shifted Turanian coefficients.",
        H("The coefficient nonnegativity assertion"), Blocks(
            Entry("gamma-product-ratio", "coeff", "Gamma product ratios",
                "For vectors a of length p and b of length q, c(t) is the product of Gamma(a(i)+t) divided by the product of Gamma(b(j)+t). Empty products equal one, so a numerator vector of length zero is allowed."),
            Entry("shifted-turanian-coefficient", "turanCoeff", "The Cauchy coefficient",
                "For natural m, delta(m) is the sum over k from zero through m of [c(mu+alpha+k)c(mu+beta+m-k)-c(mu+k)c(mu+alpha+beta+m-k)] divided by k! times (m-k)!. Subtraction in the index m-k is natural subtraction; throughout this sum k is at most m. This is the coefficient in f(mu+alpha;x)f(mu+beta;x)-f(mu;x)f(mu+alpha+beta;x), where f(mu;x) has coefficient c(mu+n)/n! at degree n."),
            Entry("parameter-elementary-symmetric", "esymm", "Elementary symmetric functions",
                "The degree k elementary symmetric function is the sum of the products over all k-element selections of parameter positions. Repeated parameter values retain their multiplicities, and the degree zero value is one."),
            Entry("symmetric-ratio-chain", "cond13", "The ratio chain",
                "For every natural j less than p, require e(q-j,b)/e(p-j,a) to be at most e(q-j-1,b)/e(p-j-1,a). With p at most q these are exactly the consecutive inequalities in the descending symmetric ratio chain. If p is zero there are no inequalities."),
            Entry("hypergeometric-coefficient-claim", "claim", "Universal coefficient nonnegativity",
                "For all p at most q and all positive parameter vectors satisfying the ratio chain, require delta(m) to be nonnegative for every natural m whenever mu is at least one, alpha and beta are nonnegative, and alpha is at most beta+1. This is the coefficient conclusion of the conjecture in the branch p at most q. Refuting this conclusion refutes the conjecture; no assertion about the value of the Turanian for nonnegative x is needed."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
