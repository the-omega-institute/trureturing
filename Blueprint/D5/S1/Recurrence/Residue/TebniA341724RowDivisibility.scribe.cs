using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class TebniA341724RowDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create("D5/L/RecurrenceComposition/tebni2023a341724");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both original A341724 row-divisibility conjectures hold for the integral coefficients of the exact column EGF.",
        H("Tebni's A341724 prime and dyadic row divisibility"),
        Blocks(
            Paragraph(Text("All indices and exponents are natural, including zero. The coefficients lie in Q, "
                + "and the inverse is the formal power-series inverse. The odd Taylor series sinh is "
                + "TebniA364822.sinh. Rescaling it by -1 substitutes -X, so the denominator is 1+2 sinh(X). "
                + "The constant series C embeds a rational scalar. Integer witnesses equal the rational "
                + "coefficients after casting to Q; the row modulus is cast to Z.")),
            Node("denominator", "The original denominator", Equal(Call("denominator"), Denominator()),
                "OEIS A341724 specifies the column denominator as 1-2 sinh(-X). Oddness of the Taylor series gives 1+2 sinh(X); in particular its constant coefficient is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("column", "The literal column EGF", All("k", Nat(), Equal(Call("column", K()), Column())),
                "The displayed product is X^k divided by k! times the original denominator. The scalar inverse and the formal inverse are taken in their respective carriers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("Tq", "Factorial-normalized column coefficients", All("n", Nat(), All("k", Nat(),
                Equal(T(N(), K()), Mul(Cast(Factorial(N()), Rat()),
                    App(Qualified("PowerSeries", "coeff"), N(), Column()))))),
                "The source array is n! times the nth ordinary coefficient of its kth column. A column has no terms below degree k and has factorial-normalized diagonal coefficient one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("claim", "Both conjectures with their complete domains", Seq(Call("claim"), Sp, Iff, Sp, Par(ClaimBody())),
                "M. Tebni's OEIS conjectures require 0<k<p at a prime row and 0<=k<2^m at a dyadic row. The prime two is included. The dyadic clause includes k=0 and m=0, when the modulus is one. Each clause asserts integrality as well as divisibility.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("result", "Prime and dyadic row divisibility", ClaimBody(),
                "Multiplying the exact column by 1+2 sinh(X) gives X^k/k!. The factorial-normalized product formula yields the forcing term equal to one precisely when n=k, minus twice the sum of choose(n,j) Tq(n-j,k) over positive odd j<=n. Strong induction gives integral coefficients, using support below the diagonal and the diagonal value one. For n>k the forcing vanishes. At a prime p every interior binomial term is divisible by p; the j=p endpoint is zero because k>0 implies Tq(0,k)=0. At a dyadic row every odd-index binomial coefficient is divisible by the row index. These arguments retain the prime two and exponent zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source()),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("tebni341724-row-divisibility"), ResolutionKind.Proved))),
        edges: [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Residue/IntegralEGFComposition")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Residue/TebniA364822")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo"))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("tebni341724-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, claim);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Named(name) : App(Named(name), args);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula Cast(Formula x, Formula type) => Par(Seq(x, Colon, Sp, type));
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Par(x), FormulaBinaryOperator.Multiply, Par(y));
    private static Formula Inv(Formula x) => new Formula.Power(Par(x), Seq(Minus, D(1)));
    private static Formula Factorial(Formula n) => App(Qualified("Nat", "factorial"), n);
    private static Formula Denominator() => Sub(D(1), Mul(D(2),
        App(Qualified("PowerSeries", "rescale"), Seq(Minus, D(1)), Qualified("TebniA364822", "sinh"))));
    private static Formula Column() => Mul(new Formula.Power(F.Id("X"), K()),
        Mul(App(Qualified("PowerSeries", "C"), Inv(Cast(Factorial(K()), Rat()))), Inv(Call("denominator"))));
    private static Formula T(Formula n, Formula k) => Call("Tq", n, k);
    private static Formula Witness(Formula index, Formula k)
    {
        var z = F.Id("z");
        return Seq(Exists, Sp, z, Colon, Sp, Ints(), Comma, Sp,
            And(Equal(Cast(z, Rat()), T(index, k)), Seq(Cast(index, Ints()), Sp, Mid, Sp, z)));
    }
    private static Formula ClaimBody()
    {
        var p = F.Id("p"); var m = F.Id("m"); var k = K();
        var index = new Formula.Power(D(2), m);
        var prime = All("p", Nat(), All("k", Nat(),
            Imp(App(Qualified("Nat", "Prime"), p), Imp(Seq(D(0), Sp, Lt, Sp, k),
                Imp(Seq(k, Sp, Lt, Sp, p), Witness(p, k))))));
        var dyadic = All("m", Nat(), All("k", Nat(),
            Imp(Seq(k, Sp, Lt, Sp, index), Witness(index, k))));
        return And(prime, dyadic);
    }
}
