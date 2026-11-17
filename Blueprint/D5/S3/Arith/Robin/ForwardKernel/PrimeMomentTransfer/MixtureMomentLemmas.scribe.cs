using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class MixtureMomentLemmasDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.";

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite algebraic moment data and biased-cube mixture identities apply at arbitrary order.",
        H("Finite-mixture moment comparisons"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fifth-data"), DeclarationHandle.Create(Prefix + "FifthData"),
                H("Finite algebraic moment data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A datum consists of a finite decidable index type, a commutative real algebra, "
                    + "a real linear functional, an indexed algebra family, and four real parameters a,b,H,L. "
                    + "Both underlying types are in universe zero; positivity is a hypothesis of the implication below."))),
                DescribeRole.Definition),
            Entry("injective-product-comparison", "inj_sum_product_bound", "An arbitrary-order collision bound",
                "Let r be positive and let N be at least r. For r real coefficient families on N indices bounded "
                + "in absolute value by one, removing noninjective assignments from the product of coefficient sums "
                + "changes its value by at most choose(r,2) N^(r-1). The number of omitted assignments is "
                + "N^r minus the descending factorial. Its recurrence bounds the next-order error by N times "
                + "the previous error plus r N^r; the binomial recursion gives the stated constant."),
            Entry("distinct-subset-universe", "subsetDistinct_univ", "The whole label set",
                "For arbitrary k, evaluating the subset distinct-index moment on all labels in Fin k "
                + "recovers the original ordered distinct-index moment by reindexing its canonical enumeration."),
            Entry("unit-weight-subset-moment", "subset_unit_moment", "Unit-weight moments of any finite mixture",
                "For arbitrary finite real bias values and weights, let m_j be the weighted j-th bias moment. "
                + "For a label subset U of cardinality j, the unit-weight distinct-index moment equals "
                + "m_j divided by (sqrt(N))^j, multiplied by the descending factorial of N of length j. "
                + "The formula counts the injective assignments and does not require positive weights."),
            Entry("distinct-pair-formula", "distinct_pair_formula", "The two-label formula",
                "For any finite bias mixture and real coefficient families f and h on N indices, "
                + "the two-label distinct moment is m_2/N times ((sum f)(sum h) minus sum(f h)). "
                + "The off-diagonal sum removes precisely the equal-index assignments."),
            Entry("subset-pair-formula", "subset_pair_formula", "Two-label subsets of any finite label type",
                "For a two-element label subset e and arbitrary real coefficient families g, its distinct moment "
                + "is m_2/N times (the product over i in e of sum_d g_i(d), minus sum_d of the product over i in e "
                + "of g_i(d)). Reindexing the two labels gives the preceding two-label formula."))));
}
