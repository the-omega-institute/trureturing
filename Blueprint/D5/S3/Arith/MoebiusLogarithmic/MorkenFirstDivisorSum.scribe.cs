using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.MoebiusLogarithmic;

internal sealed class MorkenFirstDivisorSumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/morken2026a112399first");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coprime Moebius sum equals a double sum over squarefree divisors.",
        H("Morken's first divisor-sum identity"),
        Blocks(
            Describe.Lean(DescribeId.Create("morken-first-divisor-sum"),
                DeclarationHandle.Create("D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum.result"),
                H("The identity on every positive integer"),
                StatementSource.FromAuthor(Identity()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Here n, k, d and m are natural numbers, and n is positive. "
                        + "mu is the standard integer-valued Moebius function, including mu(1)=1. "
                        + "All interval endpoints are inclusive. divisors(n) contains exactly the "
                        + "positive divisors of n, so n/d is exact integer division. The outer "
                        + "filter mu(d)!=0 restricts d, without imposing squarefreeness on n. "
                        + "The inner coprimality condition is gcd(m,d)=1, whereas the left condition "
                        + "is gcd(k,n)=1. No finite bound on n or assertion at n=0 is made.")),
                    Paragraph(Text("OEIS A112399, revision 41, FORMULA, attributes this first "
                        + "conjecture to Jamie Morken. The conjecture has "
                        + "AI-assisted provenance; that supplies no proof. The second conjecture "
                        + "in the entry and the product-parameter identity associated with A372706 "
                        + "are separate assertions.")),
                    Paragraph(Text("For positive d and m the filtered summand equals "
                        + "mu(d*m)*mu(d). If mu(d)=0 both expressions vanish. Otherwise d is "
                        + "squarefree: coprimality permits multiplicativity and mu(d)^2=1, "
                        + "while failure of coprimality makes d*m nonsquarefree. Reindex by "
                        + "k=d*m and exchange the finite sums. The coefficient of mu(k) becomes "
                        + "the sum of mu(d) over divisors of gcd(k,n). The standard Moebius "
                        + "divisor cancellation is one when gcd(k,n)=1 and zero otherwise. "
                        + "Thus the remaining sum is precisely the original coprime sum."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a112399-morken-first-divisor-sum"),
                    ResolutionKind.Proved)))));

    private static Formula Identity()
    {
        var n = F.Id("n"); var k = F.Id("k");
        var d = F.Id("d"); var m = F.Id("m");
        Formula Mu(Formula x) => Call("mu", x);
        Formula Coprime(Formula x, Formula y) => Equal(Call("gcd", x, y), D(1));
        Formula Interval(Formula x, Formula top) => Seq(D(1), Sp, Le, Sp, x, Sp, Le, Sp, top);
        Formula SumOver(Formula condition, Formula term) =>
            Seq(new Formula.Subscript(Sum, condition), term);
        var left = SumOver(Seq(Interval(k, n), Comma, Sp, Coprime(k, n)), Mu(k));
        var inner = SumOver(Seq(Interval(m, new Formula.Fraction(n, d)), Comma, Sp,
            Coprime(m, d)), Mu(m));
        var right = SumOver(Seq(d, InMacro, Call("divisors", n), Comma, Sp,
            Mu(d), Neq, D(0)), inner);
        return Disp(Seq(Forall, Sp, n, InMacro, Seq(Mathbb, Grp(F.Id("N"))), Comma,
            Sp, D(0), Lt, n, Rightarrow, Sp, Equal(left, right)));
    }
}
