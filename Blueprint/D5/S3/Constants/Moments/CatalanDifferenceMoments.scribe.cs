using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class CatalanDifferenceMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit forward differences of Catalan moments are positive and obey a uniform ratio envelope.",
        H("Catalan Difference Moment Ratios"),
        Blocks(Describe.Lean(
            DescribeId.Create("catalan-difference-ratio-envelope"),
            DeclarationHandle.Create("D5/S3/Constants/Moments/CatalanDifferenceMoments.catalan_difference_ratio_envelope"),
            H("A uniform envelope for every difference order"),
            StatementSource.FromAuthor(Disp(EnvelopeFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write M(m) for the original catalanMoment, the m-th moment of four times "
                        + "a beta variable with parameters one half and three halves. Its exact "
                        + "moment formula is M(m)=Catalan(m). For natural L and k let A(L,k) "
                        + "denote the k-fold unit forward difference of M at L. For every L at "
                        + "least one and every k, A(L,k) is strictly positive, "
                        + "3(L+k)A(L,k) is at most (L+k+2)A(L,k+1), and "
                        + "A(L,k+1) is strictly less than 3A(L,k).")),
                Paragraph(Text(
                    "The Catalan recurrence gives (L+2)A(L,1)=3L A(L,0). The shift identity "
                        + "A(L+1,k)=A(L,k)+A(L,k+1) transports this equation to "
                        + "(L+s+3)A(L,s+2)=(3L+2s+2)A(L,s+1)+3(s+1)A(L,s) "
                        + "for every natural s. Simultaneous induction preserves positivity "
                        + "and the two ratio inequalities. For the upper inequality, the "
                        + "coefficient difference (k+7)(L+k)-(k+1)(L+k+2)=6L+4k-2 "
                        + "is positive. This includes L=1, order zero, and both parities.")),
                Paragraph(Text(
                    "For every natural n at least 15, put m=floor(n/2)-4, "
                        + "c_r=Catalan(n-r-2), V_r=c_(r+2)-2c_(r+3)+c_(r+4), and "
                        + "G_d=sum_(r=0)^d (-1)^r choose(d,r) V_r-V_d. These are numerical "
                        + "definitions. For every 1 <= d <= m, the original moment formula "
                        + "gives V_r=A(n-r-6,2) for 0 <= r <= d. Reflecting the binomial "
                        + "forward-difference expansion of the function x -> A(x,2), and "
                        + "composing its d and two difference orders, gives "
                        + "G_d=A(L,d+2)-A(L,2), where L=n-d-6 >= 6. The summation bound "
                        + "r <= d and d+4 <= floor(n/2) justify every natural subtraction; "
                        + "no parity or additional lower cutoff on n is required.")),
                Paragraph(Text(
                    "At L >= 6 the positive lower envelope makes A(L,k+1)>A(L,k) "
                        + "for every natural k: the coefficient excess is 2(L+k)-2>0. "
                        + "Strict monotonicity in the order therefore gives G_d>0 for "
                        + "1 <= d <= m. If 1 <= d < m, set L'=n-d-7 >= 6. The shift "
                        + "identity gives G_d-G_(d+1)=A(L',d+2)-A(L',3) >= 0. "
                        + "Finally direct expansion gives G_1=G_2=V_0-2V_1="
                        + "c_2-4c_3+5c_4-2c_5=h_n. This establishes the full numerical "
                        + "positivity, monotonicity and endpoint equalities. It does not "
                        + "identify any number with an actual trace fiber, establish a "
                        + "partition or total-cardinality identity, or construct compatible ears.")),
                Paragraph(Text(
                    "For n at least 34, 1 <= d <= floor(n/2)-4 and 0 <= r < d, define "
                        + "omega(n,d,r) as the sum from j=0 through d-r+2 of "
                        + "(-1)^j choose(d-r+2,j) Catalan(n-r-j-4). The binomial expansion "
                        + "of the forward difference, with the summation index reflected, "
                        + "identifies this sum with A(L,k) for L=n-d-6 and k=d-r+2. "
                        + "Every index satisfies j <= k, so natural subtraction agrees with "
                        + "the indicated integer indices. These parameters obey L >= 15, "
                        + "k >= 3 and L+k=n-r-4 >= 18. Incrementing r reduces k by one; "
                        + "the endpoint r=d-1 therefore compares orders three and two.")),
                Paragraph(Text(
                    "Put s=L+k. The lower envelope at k-1 and positivity imply "
                        + "A(L,k-1)/A(L,k) <= (s+1)/(3(s-1)). For s >= 18 this is at most "
                        + "19/51, which is strictly less than 28561/76415: the cross-product "
                        + "margin 51*28561-19*76415 is 4726. Thus omega(n,d,r+1) "
                        + "<= (28561/76415) omega(n,d,r) throughout the stated domain. "
                        + "This is a bound for the numerical count sequence. Identifying "
                        + "an actual polygon completion fiber and deriving a bound for a "
                        + "common intersecting family require their own combinatorial hypotheses."))),
            DescribeRole.Theorem))));

    private static Formula EnvelopeFormula()
    {
        Formula l = F.Id("L");
        Formula k = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula value = A(l, k);
        Formula next = A(l, Seq(k, Plus, D(1)));
        Formula total = Seq(l, Plus, k);
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, value);
        Formula lower = new Formula.Relation(
            Seq(D(3), Cdot, Par(total), Cdot, value),
            FormulaRelationOperator.LessThanOrEqual,
            Seq(Par(Seq(total, Plus, D(2))), Cdot, next));
        Formula upper = new Formula.Relation(next, FormulaRelationOperator.LessThan,
            Seq(D(3), Cdot, value));
        Formula conclusion = new Formula.Logic(positive, FormulaLogicOperator.And,
            new Formula.Logic(Par(lower), FormulaLogicOperator.And, Par(upper)));
        Formula hypothesis = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, l);
        return Quantify("L", naturals, Quantify("k", naturals, Implication(hypothesis, conclusion)));
    }

    private static Formula A(Formula l, Formula k) =>
        Seq(Operatorname, Grp(F.Id("A")), Open, l, Comma, k, Close);

    private static Formula Par(Formula formula) => Seq(Open, formula, Close);

    private static Formula Quantify(string name, Formula type, Formula body) => Seq(Forall, Sp,
        Par(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, Par(body));

    private static Formula Implication(Formula premise, Formula conclusion) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, Par(conclusion));
}
