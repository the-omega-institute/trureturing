using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class GridAntidiagonalTrafficBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/gil2026grid");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform strict binomial-ratio bound for antidiagonal grid obstructions at every n at least 496.",
        H("A Uniform Bound for Antidiagonal Grid Traffic"),
        Blocks(
            Paragraph(Text(
                "Gil, Liang, Odetola and Weiner consider north-east lattice paths from (0,0) "
                + "to (n,n) avoiding an obstruction B. Their Conjecture 7.4 concerns the points "
                + "of maximum traffic when B lies on x+y=n. The arithmetic theorem below "
                + "establishes a stronger sufficient strict inequality. The grid and path-count "
                + "statements used to obtain the ordinary grid conclusion are published "
                + "literature inputs; they are not Lean-verified in this module.")),
            Describe.Lean(
                DescribeId.Create("strict-arithmetic-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The rational traffic ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let n and a be natural numbers with n at least 496, a at least one, "
                        + "and 2a<n. Binomial coefficients are natural numbers, and the divisions "
                        + "in the following ratio take place in the rational numbers:"),
                        Math(F.Disp(Equal(Call("R", Id("n"), Id("a")), Ratio())))),
                    Paragraph(Text(
                        "The proposition claim says R(n,a)<1 for every such pair, without an "
                        + "upper bound on n. In particular it includes a=1 and the odd near-central "
                        + "pair (n,a)=(497,248). The condition 2a<n uses no truncated division by two. "
                        + "All subtractions occurring in binomial indices and denominators are "
                        + "nonnegative on this domain, and both denominators are positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-strict-bound"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The uniform strict inequality"),
                StatementSource.FromAuthor(F.Disp(UniversalBound())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Put k=n-2a and write T(n,k)=R(n,(n-k)/2) on the domain k>=1, "
                        + "n>=k+2 and n congruent to k modulo two. The identity "
                        + "choose(n-2,a-1)=a(n-a)choose(n,a)/(n(n-1)) gives"),
                        Math(F.Disp(Equal(Call("T", Id("n"), Id("k")), NormalForm())))),
                    Paragraph(Text(
                        "First fix n. Lowering a by one increases k by two, and the quotient "
                        + "of successive T values is (n-k)(n-k-2)(k+3)/((n+k+2)^2(k+1)). "
                        + "Its numerator minus denominator is -2F(n,k), where "
                        + "F(n,k)=2k^2 n+7kn+k-n^2+5n+2. For n>=496 and 1<=k<=14, "
                        + "F(n,k)<=-n^2+495n+16<0. Thus every small-gap value is bounded "
                        + "above by a value in the same row with k>=15. The move is always "
                        + "legal: these small gaps force a>=2. Repetition terminates because a "
                        + "decreases. Parity gives k>=16 in even rows; odd rows can retain k=15.")),
                    Paragraph(Text(
                        "Next fix k>=3 and let n vary with the same parity. The exact quotient is"),
                        Math(F.Disp(Equal(
                            Divide(Call("T", Add(Id("n"), Num(2)), Id("k")),
                                Call("T", Id("n"), Id("k"))), FixedGapRatio())))),
                    Paragraph(Text(
                        "Let Delta(n,k) be the numerator minus denominator of this quotient, "
                        + "and put x=n-k>0. Dividing Delta(k+x,k) by x^5 gives -4 plus five "
                        + "positive coefficients times 1/x, 1/x^2, ..., 1/x^5. The coefficients "
                        + "are positive for k>=3, as their expansions in k-3 have positive "
                        + "coefficients. Hence this expression decreases with x. For e=0 or 1, "
                        + "direct polynomial factorization gives Delta(N-2,k)>0 and Delta(N,k)<0 "
                        + "at N=2k(k+1)-e. Taking e to be the parity of k, the same-parity "
                        + "sequence therefore increases up to N and decreases after N. "
                        + "In particular, T(n,k)<=T(N,k) for every admissible n.")),
                    Paragraph(Text(
                        "It remains to bound these infinitely many peaks. For positive m, "
                        + "the pinned Stirling successive-difference estimate is "
                        + "log(s_m)-log(s_(m+1))<=1/(12m(m+1)), with s_m tending to sqrt(pi). "
                        + "Consequently log(s_m)-1/(12m) is increasing to log(sqrt(pi)). "
                        + "This supplies the upper logarithmic factorial remainder 1/(12m); "
                        + "the Stirling lower bound supplies the denominator estimates. "
                        + "These established Stirling results are used inside the peak argument.")),
                    Paragraph(Text(
                        "For 0<=x<1, set h(x)=(1-x)log(1-x)+(1+x)log(1+x). "
                        + "The logarithmic series lower bound gives "
                        + "h'(x)=log((1+x)/(1-x))>=2x. Since h(0)=0, one obtains h(x)>=x^2. "
                        + "Apply this with x=k/n, and combine the upper estimates for n! and "
                        + "(n-1)! with the lower estimates for a!, (n-a)! and (2n-2)!. "
                        + "Cancellation in the logarithm of T gives the weak bound T(n,k)<=B(n,k), "
                        + "where"),
                        Math(F.Disp(Equal(Call("B", Id("n"), Id("k")), Envelope())))),
                    Paragraph(Text(
                        "Each parity envelope B(2k(k+1)-e,k) decreases for real k>=3. "
                        + "The two remainder terms decrease because 2k(k+1)-e increases. "
                        + "The logarithmic derivative of the remaining factor for e=0 is "
                        + "-(4k^3+20k^2+28k+11)/(2(k+1)^2(2k+3)(2k^2+2k-1)), which is negative. "
                        + "For e=1 it is -P(k)/(2(k+1)(k^2+k-1)(2k^2+2k-1)^2(2k^2+3k-1)), "
                        + "where P(k)=8k^7+48k^6+80k^5+12k^4-52k^3-3k^2+20k-5. "
                        + "Expanding P in k-2 gives positive coefficients, so this derivative "
                        + "is also negative throughout the required interval.")),
                    Paragraph(Text(
                        "At the even base (N,k)=(544,16), it suffices to prove "
                        + "5345344/665175 < pi exp(832961/886176). At the odd base "
                        + "(N,k)=(611,17), it suffices to prove "
                        + "60478002/7517945 < pi exp(352173/372710). Both follow by rational "
                        + "arithmetic from pi>157/50 and the positive exponential Taylor sums "
                        + "through degrees six and four, respectively. Monotonicity now bounds "
                        + "every even peak with k>=16 and every odd peak with k>=17 strictly "
                        + "below one. This is the uniform peak estimate used by the theorem.")),
                    Paragraph(Text(
                        "The remaining odd gap k=15 has its peak at N=479. Thus its sequence "
                        + "decreases over all odd n>=497. The exact local certificate "
                        + "241 choose(497,241)^2 < 31 choose(992,496) gives "
                        + "T(497,15)=R(497,241)<1. Together with the low-gap ascent and "
                        + "the uniform large-gap estimate, this bounds every original R(n,a) "
                        + "strictly below one. Casting between the rational and real expressions "
                        + "preserves the inequality.")),
                    Paragraph(Text(
                        "To recover the ordinary grid conclusion, use Section 6 of "
                        + "arXiv:2609.01562v1. For n>=9 it reduces the maximum to six "
                        + "corner-adjacent points except for obstructions in "
                        + "{(1,2),(2,1),(n-1,n-2),(n-2,n-1)}. Their coordinate sums are "
                        + "3 or 2n-3, neither of which equals n when n>=496. "
                        + "For an interior obstruction B=(a,n-a) with 2a<n, Proposition 7.1 "
                        + "pairs opposite candidates and identifies (1,0) as the larger "
                        + "boundary competitor. Proposition 7.2 gives "
                        + "f_B(1,0)-f_B(1,1)=D(n)(R(n,a)-1), with "
                        + "D(n)=choose(2n-2,n-1)/n>0. The strict arithmetic bound defeats "
                        + "that competitor, so both (1,1) and (n-1,n-1) attain the maximum.")),
                    Paragraph(Text(
                        "Equation (2.1), using coordinate interchange, covers the interior "
                        + "half 2a>n. At the even central obstruction 2a=n, Theorem 5.1 applies "
                        + "because n>=496 implies n>=5; its two cases give the two near-corner "
                        + "maximizers. At a=0 or a=n, Lemma 2.2(ii) and (iii) both apply and "
                        + "give the same conclusion. This accounts for every antidiagonal "
                        + "obstruction in the published conjecture. These grid reductions "
                        + "remain literature inputs, not Lean grid/path theorems here. "
                        + "Only the sufficient implication from R<1 is used; no converse "
                        + "or assertion excluding other tied maximizers is made."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gil-liang-odetola-weiner-antidiagonal-traffic"),
                    ResolutionKind.Proved)))));

    private static Formula Ratio()
    {
        var n = Id("n");
        var a = Id("a");
        return Divide(
            Multiply(Multiply(Divide(Multiply(n, Add(Subtract(n, Multiply(Num(2), a)), Num(1))),
                Subtract(n, a)), Choose(n, a)), Choose(Subtract(n, Num(2)), Subtract(a, Num(1)))),
            Choose(Subtract(Multiply(Num(2), n), Num(2)), Subtract(n, Num(1))));
    }

    private static Formula UniversalBound()
    {
        var n = Id("n");
        var a = Id("a");
        Formula premise = And(Le(Num(496), n), And(Le(Num(1), a), Lt(Multiply(Num(2), a), n)));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
             new Formula.BoundVariable(FormulaIdentifier.Create("a"), Naturals())],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, Lt(Ratio(), Num(1))));
    }

    private static Formula NormalForm()
    {
        var n = Id("n");
        var k = Id("k");
        return Multiply(Divide(Multiply(Subtract(n, k), Add(k, Num(1))),
                Multiply(Num(2), Subtract(n, Num(1)))),
            Divide(Pow(Choose(n, Divide(Subtract(n, k), Num(2))), 2),
                Choose(Subtract(Multiply(Num(2), n), Num(2)), Subtract(n, Num(1)))));
    }

    private static Formula FixedGapRatio()
    {
        var n = Id("n");
        var k = Id("k");
        return Divide(
            Multiply(Multiply(Multiply(Multiply(Num(4), n), Subtract(n, Num(1))),
                Pow(Add(n, Num(1)), 2)), Pow(Add(n, Num(2)), 2)),
            Multiply(Multiply(Multiply(Multiply(Subtract(n, k), Add(Subtract(n, k), Num(2))),
                Subtract(Multiply(Num(2), n), Num(1))), Add(Multiply(Num(2), n), Num(1))),
                Pow(Add(Add(n, k), Num(2)), 2)));
    }

    private static Formula Envelope()
    {
        var n = Id("n");
        var k = Id("k");
        var exponent = Add(Subtract(Divide(Num(1), Multiply(Num(6), n)), Divide(Pow(k, 2), n)),
            Divide(Num(1), Multiply(Num(6), Subtract(n, Num(1)))));
        return Multiply(Divide(Multiply(Multiply(Num(4), n), Add(k, Num(1))),
                Multiply(Add(n, k), Call("sqrt", Multiply(F.Pi, Subtract(n, Num(1)))))),
            Call("exp", exponent));
    }

    private static Formula Choose(Formula n, Formula a) => Call("choose", n, a);
    private static Formula Divide(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, long n) => new Formula.Power(x, Num(n));
    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
}
