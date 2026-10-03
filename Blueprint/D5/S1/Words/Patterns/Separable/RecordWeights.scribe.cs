using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class RecordWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right maxima give suffix weights under direct sums and additive weights under skew sums.",
        H("Signed record weights on separable permutations"),
        Blocks(
            Paragraph(Text(
                "For a permutation pi of {0,...,n-1}, a right maximum is a position i such that "
                + "pi(j)<pi(i) for every j>i. Write r(pi) for the number of these positions. "
                + "The count is strict and unshifted. A left minimum satisfies pi(i)<pi(j) for all j<i; "
                + "a left maximum satisfies pi(j)<pi(i) for all j<i; a right minimum satisfies "
                + "pi(i)<pi(j) for all j>i. Separable permutations here are exactly the permutations "
                + "avoiding the classical patterns 2413 and 3142.")),
            Paragraph(Text(
                "For permutations a and b of lengths m and h, direct(a,b) places a below b in value "
                + "and before b in position; skew(a,b) places a above b and before b. Neither factor "
                + "is reversed. A proper cut c satisfies 0<c<n. Sign false means a direct cut, with "
                + "every prefix value below every suffix value; sign true means a skew cut, with "
                + "every prefix value above every suffix value.")),
            Describe.Lean(
                DescribeId.Create("actual-record-block-sum-laws"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/RecordWeights.rmax_block_sum"),
                H("Right maxima in arbitrary direct and skew sums"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("r", Call("direct", F.Id("a"), F.Id("b"))), Eq,
                    Call("ite", Seq(F.Id("h"), Eq, D(0)), Call("r", F.Id("a")), Call("r", F.Id("b"))),
                    Sp, Land, Sp,
                    Call("r", Call("skew", F.Id("a"), F.Id("b"))), Eq,
                    Call("r", F.Id("a")), Plus, Call("r", F.Id("b"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "These identities hold for every pair of natural lengths m,h and every "
                        + "permutation a of length m and b of length h, without an avoidance hypothesis. "
                        + "If h>0, every prefix position of a direct sum has a larger suffix value, so "
                        + "none is a right maximum. Suffix positions are right maxima exactly when "
                        + "they are right maxima in b. If h=0, the direct sum has the records of a. "
                        + "In a skew sum all prefix values exceed all suffix values, so a prefix "
                        + "position is a right maximum exactly when it is one in a. Suffix records "
                        + "again coincide with those of b. The two disjoint sets of positions give "
                        + "the additive count, also when either factor is empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-weighted-minimum-cut-convolution"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/RecordWeights.proper_cut_record_convolution"),
                H("Proper-cut record fibers"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, F.Id("n"), Comma, F.Id("k"), Comma, Sp,
                    Call("D", F.Id("s"), F.Id("n"), F.Id("k")), Eq,
                    Call("C", F.Id("s"), F.Id("n"), F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n,k and sign s in {false,true}, let A(n) be the separable "
                        + "permutations of length n, B(s,n) those with no proper cut of sign s, and "
                        + "P(s,n) those with a proper cut of sign s. Define U(n,k) as the number of "
                        + "members of A(n) with r=k, J(s,n,k) as the number of members of B(s,n) "
                        + "with r=k, j(s,n) as the cardinality of B(s,n), and D(s,n,k) as the "
                        + "number of members of P(s,n) with r=k. Define C by the following formulas.")),
                    new DocumentBlock.DisplayFormula(Disp(Seq(
                        Call("C", F.Id("false"), F.Id("n"), F.Id("k")), Eq,
                        Sum, Underscore, Grp(D(0), Lt, F.Id("c"), Lt, F.Id("n")), Sp,
                        Call("j", F.Id("false"), F.Id("c")), Cdot,
                        Call("U", Seq(F.Id("n"), Minus, F.Id("c")), F.Id("k"))))),
                    new DocumentBlock.DisplayFormula(Disp(Seq(
                        Call("C", F.Id("true"), F.Id("n"), F.Id("k")), Eq,
                        Sum, Underscore, Grp(D(0), Lt, F.Id("c"), Lt, F.Id("n")), Sp,
                        Sum, Underscore, Grp(D(0), Le, F.Id("b"), Le, F.Id("k")), Sp,
                        Call("J", F.Id("true"), F.Id("c"), F.Id("b")), Cdot,
                        Call("U", Seq(F.Id("n"), Minus, F.Id("c")),
                            Seq(F.Id("k"), Minus, F.Id("b")))))),
                    Paragraph(Text(
                        "Both sums range over natural numbers. Each cut gives lengths c and n-c, "
                        + "both positive, with c+(n-c)=n. In the skew sum, 0<=b<=k ensures that k-b "
                        + "is the actual suffix record count. The equation holds for all k, including "
                        + "k>n, and for n=0 or n=1, when there are no proper cuts and both sides vanish.")),
                    Paragraph(Text(
                        "Choose the least proper cut of sign s. The prefix has no proper cut of "
                        + "that sign, and the standardized prefix and suffix both avoid 2413 and 3142. "
                        + "Conversely, a pair in B(s,c) times A(n-c) reconstructs a unique member "
                        + "of P(s,n) whose least cut is c. The block identities preserve the right-maximum "
                        + "count under this correspondence. For a direct cut the fiber is "
                        + "B(false,c) times the suffix fiber of record count k. For a skew cut it is "
                        + "the disjoint union over b of the prefix fiber of count b times the suffix "
                        + "fiber of count k-b. Counting these disjoint products gives the two formulas.")),
                    Paragraph(Text(
                        "The empty permutation has zero records and lies in each B(s,0). In the "
                        + "paper's convention an irreducible permutation has positive length and no "
                        + "proper direct cut; a reducible permutation has a proper direct cut. Thus "
                        + "the empty permutation is in neither paper class, the singleton is irreducible, "
                        + "and there are no reducible permutations of length one.")),
                    Paragraph(Text(
                        "References: Joanna N. Chen, Sergey Kitaev and Philip B. Zhang, Distributions "
                        + "of statistics on separable permutations, arXiv:2404.18517v1, Sections 1.2 "
                        + "and 2; Discrete Applied Mathematics 355 (2024), 169-179, "
                        + "DOI 10.1016/j.dam.2024.05.004. The signed decomposition also appears in "
                        + "Fu, Lin and Zeng, On two unimodal descent polynomials, Proposition 2.1.")),
                    Paragraph(Text(
                        "The published Section 3 Conjecture 2 asks, for every n>=5 and k>=0, "
                        + "that the irreducible rmax/lmin and reducible lmax/rmin counts increase "
                        + "weakly from k to k+1 when k<3, decrease weakly when k>=3, and have a "
                        + "maximum at 3. These two identities do not supply those inequalities, "
                        + "the full record generating-function identification, or the transports "
                        + "between the four record statistics."))),
                DescribeRole.Theorem))));
}
