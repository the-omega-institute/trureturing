using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class DeformedJucysMurphyC2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered Coulter–Do differential operator has a partition basis, a nonzero normalization, detailed balance, and a normalized transposed coefficient expansion over RatFunc Complex.",
        H("The Algebraic Coulter–Do Operator and Its Normalized Expansion"),
        Blocks(
            Paragraph(Text("The algebra is K[p_1,p_2,...], with weight(p_r)=r and positive r. "
                + "Lean variable n represents p_(n+1). A partition rho represents the monomial p_rho with "
                + "the actual part multiplicities as exponents. All natural weights are retained, including "
                + "weight zero and the empty monomial. For a general characteristic-zero field and b in K, "
                + "D_b is one half of the following three-term sum: (1+b) times the ordered sum of "
                + "i*j*p_(i+j)*partial_i*partial_j; the ordered sum of (i+j)*p_i*p_j*partial_(i+j); "
                + "and b times the sum of "
                + "i*(i-1)*p_i*partial_i. Both double sums run over all positive ordered pairs. "
                + "The operator is the linear extension of actual derivatives on every monomial. "
                + "On the full homogeneous component of weight k its literal formula uses bound k; "
                + "a derivative index exceeding that weight has zero monomial exponent. "
                + "For a polynomial mixing weights, apply this argument to each of its finitely many monomials. "
                + "This support observation describes the infinite operator, without a separate mixed-weight endpoint.")),
            Describe.Lean(DescribeId.Create("partition-expansion"),
                DeclarationHandle.Create(Prefix + "homogeneous_expansion"),
                H("All-Partition Expansion of a Homogeneous Polynomial"),
                StatementSource.FromAuthor(Expansion()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For this first statement K is any commutative semiring. "
                    + "The exponent-to-partition construction is inverse to the multiplicity map. "
                    + "Coefficient extraction and injectivity then give the expansion over every partition of k."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the remaining statements fix K=RatFunc Complex, beta=X and alpha=1+X. "
                + "Write B(rho,sigma) for the coefficient of p_sigma in D_beta(p_rho). "
                + "Let m_r(rho) be the number of parts equal to r, z_rho the product of "
                + "r^m_r(rho) times m_r(rho)! over the finite part support, and "
                + "A_rho=alpha^(number of parts of rho)*z_rho.")),
            Describe.Lean(DescribeId.Create("normalization-nonzero"),
                DeclarationHandle.Create(Prefix + "normalization_ne_zero"),
                H("Every Partition Normalization Is Nonzero"),
                StatementSource.FromAuthor(OverPartition("rho",
                    new Formula.Relation(Call("A", V("rho")), FormulaRelationOperator.NotEqual, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial 1+X has nonzero coefficient at degree one and stays "
                    + "nonzero in the rational function field. Each positive part power and factorial is positive, "
                    + "and its characteristic-zero image is nonzero. Positive part r is variable r-1, "
                    + "so its exponent is the multiplicity m_r. Reindexing the finite exponent product "
                    + "by r=i+1 gives product_r r^m_r*m_r!, including the empty product. "
                    + "This is source correspondence, with no separate normalization wrapper."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("detailed-balance"),
                DeclarationHandle.Create(Prefix + "operatorCoefficient_balance"),
                H("Detailed Balance for Every Partition Pair"),
                StatementSource.FromAuthor(OverPartition("lambda", All("mu", Call("Partition", V("k")),
                    Equal(Mul(Call("A", V("lambda")), Call("B", V("mu"), V("lambda"))),
                        Mul(Call("A", V("mu")), Call("B", V("lambda"), V("mu"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal polynomial pairing has squared monomial norm "
                    + "alpha^length times z. Multiplication by p_i is adjoint to alpha*i*partial_i. "
                    + "Consequently each ordered join is adjoint to its ordered cut, and each Euler diagonal "
                    + "term is self-adjoint. This proves balance uniformly for equal parts, repeated parts, "
                    + "empty residuals, both transition directions, diagonal pairs and unrelated pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-expansion"),
                DeclarationHandle.Create(Prefix + "normalized_operatorCoefficient_C2"),
                H("The Normalized Expansion in the Original Coefficient Orientation"),
                StatementSource.FromAuthor(OverPartition("lambda",
                    Equal(PartitionSum("mu", Mul(
                            Fraction(Call("B", V("mu"), V("lambda")), Call("A", V("mu"))),
                            Call("p", V("mu")))),
                        Call("D", Mul(Fraction(D(1), Call("A", V("lambda"))),
                            Call("p", V("lambda"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide detailed balance by the two nonzero normalizations and use "
                    + "the partition expansion of the literal operator. The left coefficient is B(mu,lambda). "
                    + "The theorem holds at every natural weight, hence in particular at every positive weight. "
                    + "The companion occurrence source proves B(rho,sigma)=rowCoefficient beta rho sigma "
                    + "from erased occurrences, ordered cuts and the diagonal choose identity. It combines this "
                    + "with the canonical native C1 theorem and actual matching realization, giving a unique "
                    + "common coefficient function in the original conjecture."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula OverPartition(string name, Formula body) =>
        Disp(All("k", V("Nat"), All(name, Call("Partition", V("k")), body)));
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Cdot, Grp(b));
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula PartitionSum(string name, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), InMacro, Call("Partition", V("k"))), Grp(body));
    private static Formula Expansion() => Disp(All("K", V("CommSemiring"), All("k", V("Nat"),
        All("f", Call("PowerSum", V("K")),
            new Formula.Logic(Call("WeightedHomogeneous", V("f"), V("k")),
                FormulaLogicOperator.Implies,
                Equal(V("f"), PartitionSum("rho", Mul(Call("coeff", V("f"), V("rho")),
                    Call("p", V("rho"))))))))));
}
