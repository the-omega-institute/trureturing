using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class ReciprocalSigmaThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/ReciprocalSigmaThreshold.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/krizek2015a265714");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, Formula x) => Seq(Operatorname, Grp(F.Id(name)), Parenthesized(x));
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, type));
    private static Formula G(Formula k) => Call("g", k);
    private static Formula PositiveSet(Formula predicate) => Seq(OpenBrace, F.Id("k"), Colon, Nat, Sp, Mid, Sp, D(0), Lt, F.Id("k"), Sp, Land, Sp, predicate, CloseBrace);
    private static Formula CommonMinimum()
    {
        var r = F.Id("r"); var k = F.Id("k"); var m = F.Id("m");
        var a = PositiveSet(Seq(Lfloor, Sp, G(k), Rfloor, Sp, Eq, Sp, Cast(r, Ints)));
        var b = PositiveSet(Seq(Cast(r, Rat), Sp, Le, Sp, G(k)));
        return Seq(Forall, Sp, r, Colon, Nat, Comma, Sp, D(0), Lt, r, Sp, Implies, Sp,
            Exists, Sp, m, Colon, Nat, Comma, Sp, Call("IsLeast", Seq(a, Comma, m)), Sp, Land, Sp, Call("IsLeast", Seq(b, Comma, m)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal sigma sums and the first crossing of every positive integer threshold.", H("Reciprocal Sigma Threshold Minima"), Blocks(
            Describe.Lean(DescribeId.Create("reciprocal-sigma-sum"), DeclarationHandle.Create(Prefix + "g"), H("Exact divisor sum"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Nat, Comma, Sp, G(F.Id("k")), Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("d"), Sp, InMacro, Sp, Call("divisors", F.Id("k"))), Sp,
                    Frac, Grp(D(1)), Grp(Cast(Seq(SigmaLower, Underscore, D(1), Parenthesized(F.Id("d"))), Rat))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For every natural k, g(k) is the exact rational sum over k.divisors. For positive k these are all its positive divisors. "
                    + "ArithmeticFunction.sigma 1 d is the natural sum of all positive divisors of d, cast to the rationals before division. "
                    + "The empty divisor set gives g(0)=0; the two sets below require positive integers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("common-positive-minimum"), DeclarationHandle.Create(Prefix + "claim"), H("The two positive sets"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("claim"), Sp, Iff, Sp, CommonMinimum()))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("This proposition expresses the common-minimum conjecture in OEIS A265714 revision 23. "
                    + "IsLeast(S,m) means that m belongs to S and is at most every member of S. The one witness m therefore makes both sets nonempty "
                    + "and is their common least element. Int.floor is the ordinary floor of the exact rational g(k). Its value is compared with the integer cast "
                    + "of r, whereas the threshold uses the rational cast. Both r and k are unbounded, and r=1 is included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threshold-minima"), DeclarationHandle.Create(Prefix + "result"), H("A common least element"),
                StatementSource.FromAuthor(Disp(CommonMinimum())), AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Prime divisor terms bound g below by sums of 1/(p+1). Divergence of the reciprocal-prime sum ensures that every threshold is attained. "
                        + "Choose the least positive m with g(m) at least r. If m=1, the identity g(1)=1 settles the floor bound.")),
                    Paragraph(Text("Otherwise let P be the largest prime divisor of m. Multiplicativity and g(p^a) <= p/(p-1), followed by the telescoping product over "
                        + "the integers from 2 to P, give g(m)<=P. Deleting one copy of P gives a positive q<m with g(m)<=g(q)(1+1/(P+1)). Minimality gives g(q)<r; "
                        + "since r<=P this yields r<=g(m)<r+1. Thus floor(g(m))=r. Every positive k with floor(g(k))=r also has g(k)>=r, proving leastness for both sets.")),
                    Paragraph(Text("Krizek posed the source conjecture. Israel's prior observations include multiplicativity, the prime formula, divergence and "
                        + "existence of every level. The prime-power expansion is an elementary consequence of the divisor-sum definition. "
                        + "The common-minimum proof here is a repository derivation; the citation supplies the question and those observations. "
                        + "No integrality assertion about values above one or proposed numerical minima at later indices is included."))), DescribeRole.Theorem))));
}
