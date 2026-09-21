using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class A398542PolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/A398542Polynomial.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/norton2026a398542");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational polynomial witnesses for every actual fixed-bottom completion count.",
        H("The A398542 fixed-bottom polynomial theorem"),
        Blocks(
            Paragraph(Text(
                "The target is the exact fixed-bottom conjecture in OEIS A398542 "
                + "revision 18, August 30, 2026. "
                + "Perm(m) denotes permutations of Fin(m), translated to the source's "
                + "1,...,m by adding one. Avoid132(b) means not Contains(pattern132,b). "
                + "Every series below is a formal series over Q; no analytic "
                + "convergence is assumed. The Library note bounds the prior-source "
                + "comparison and makes no worldwide-priority claim.")),
            Node("intervalSeries", "The series of actual cardinalities",
                "For every b in Perm(m) and l,h in N, intervalSeries(b,l,h) "
                + "is the element of Q[[X]] whose coefficient of X^k, for every "
                + "k in N, is the rational cast of intervalCount(b,l,h,k). "
                + "These are cardinalities of actual restricted source permutations."),
            Node("catalanQ", "The pinned Catalan series over Q",
                "catalanQ is Mathlib's catalanSeries over N mapped coefficientwise "
                + "to Q by the natural-number cast ring homomorphism. Write C for "
                + "this series. The proof uses its existing identity C^2*X+1=C."),
            Node("centralSeries", "The inverse of the constant-one series",
                "centralSeries, written T, is invOfUnit(1-2X*catalanQ,1). The "
                + "specified unit is the rational unit one. The constant coefficient "
                + "of 1-2XC is one; the live proofs discharge this condition before "
                + "applying the inverse identity. No field structure on Q[[X]] "
                + "is assumed."),
            Node("actual_series", "The exact interval equation and singleton series",
                "For every m and every b in Perm(m) avoiding 132, let F(l,h)="
                + "intervalSeries(b,l,h). For all l<=h<=m, "
                + "F(l,h)=1+X*sum over g in [l,h] of "
                + "F(l,g)*F(g,min(h,dead(b,g)-1)). In addition, for every g<=m, "
                + "F(g,g)=catalanQ. The equation comes from the actual cardinal "
                + "convolution; strong coefficient induction identifies the "
                + "singleton solution uniformly from the actual recurrence.", DescribeRole.Theorem),
            Node("guarded_polynomial", "The guarded inverse-power polynomial",
                "For every m, b in Perm(m) avoiding 132, and natural l<h<=m "
                + "satisfying h<dead(b,l), there exists A in Q[X] with "
                + "A.natDegree<=2*(h-l)-2 and "
                + "intervalSeries(b,l,h)=T*A.eval2(PowerSeries.C,T). Here T="
                + "centralSeries. A uniform induction on the interval width "
                + "separates both endpoint terms, uses smaller guarded children, "
                + "and treats singleton right children by the Catalan identity. "
                + "The guard is strict and no monotonicity of dead is used.",
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The entire fixed-bottom conjecture"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural m>=1 and every b in Perm(m) avoiding 132, "
                    + "there exist rational polynomials p and q, chosen before k, "
                    + "with p.natDegree<=m-1 and q.natDegree<=m-2 and with q=0 "
                    + "when m=1, such that the displayed identity holds for every "
                    + "natural k, including zero. In the formula d(b,k) is "
                    + "Nat.card of the actual subtype of permutations w in "
                    + "Perm(m+k) whose list of values below m equals the list "
                    + "of b's values, which avoid 1324, and whose upper-value "
                    + "subsequence, read in position order and reduced by m, "
                    + "avoids 213. Thus the value cut is fixed, empty upper cells "
                    + "are allowed, and the actual recurrence gives d(b,0)=1. "
                    + "Nat.choose(2*k,k) is exactly Nat.centralBinom k in Lean. "
                    + "The natural subtractions in the degree bounds truncate "
                    + "at zero; the separate m=1 condition gives the source's "
                    + "negative-degree convention q=0. For m>=2 these are the "
                    + "ordinary degree upper bounds, also allowing zero polynomials. "
                    + "The proof applies guarded_polynomial to [0,m], whose "
                    + "guard follows from dead(b,0)=m+2. It uses the pinned "
                    + "binomial-series and Pochhammer identities directly to "
                    + "extract odd and even powers, including all nonzero "
                    + "denominator obligations. This settles the quoted fixed-bottom assertion "
                    + "alone. It does not enumerate unrestricted 1324 avoiders, "
                    + "compute the full L-gridding generating function, or settle "
                    + "A398446. Worldwide priority remains unclaimed."))), DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula ResultFormula() => Disp(Seq(
        Forall, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        D(1), Le, Sp, F.Id("m"), Rightarrow, Sp,
        Forall, Sp, F.Id("b"), InMacro, Call("Perm", F.Id("m")), Comma, Sp,
        Call("Avoid132", F.Id("b")), Rightarrow, Sp,
        Exists, Sp, F.Id("p"), Comma, F.Id("q"), InMacro,
        Mathbb, Grp(F.Id("Q")), OpenBracket, F.Id("X"), CloseBracket, Comma, Sp,
        Call("natDegree", F.Id("p")), Le, Sp, F.Id("m"), Minus, D(1), Land, Sp,
        Call("natDegree", F.Id("q")), Le, Sp, F.Id("m"), Minus, D(2), Land, Sp,
        Open, F.Id("m"), Eq, D(1), Rightarrow, Sp, F.Id("q"), Eq, D(0), Close, Land, Sp,
        Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Call("d", F.Id("b"), F.Id("k")), Eq,
        Call("p", F.Id("k")), Cdot,
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("Nat"), Dot, F.Id("choose"))),
            [Seq(D(2), Cdot, Sp, F.Id("k")), F.Id("k")]), Plus,
        Call("q", F.Id("k")), Cdot, D(4), Caret, Grp(F.Id("k"))));
}
