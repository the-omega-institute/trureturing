using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class TebniA364822Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/TebniA364822.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create("D5/L/RecurrenceComposition/tebni2023a364822");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral hyperbolic EGF coefficients have residue two at every odd prime.",
        H("Tebni's A364822 congruence at odd primes"),
        Blocks(
            Paragraph(Text("All indices are natural numbers. PowerSeries has rational coefficients. "
                + "The inverse is the formal power-series inverse, and factorials and integer "
                + "coefficients are cast to the displayed carrier. Natural subtraction in n-k "
                + "is truncated subtraction. Finset.range n contains the indices k<n. "
                + "Int.ModEq uses an integer modulus. The entry is unpaginated.")),
            Node("cosh", "The even Taylor series", Equal(Call("cosh"), Taylor(true)),
                "OEIS A364822, Name (unpaginated): \"Expansion of e.g.f. cosh(x) / (1 - 2*sinh(x)).\" The series cosh has coefficient 1/n! at even indices and zero at odd indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("sinh", "The odd Taylor series", Equal(Call("sinh"), Taylor(false)),
                "OEIS A364822, Name (unpaginated): \"Expansion of e.g.f. cosh(x) / (1 - 2*sinh(x)).\" The series sinh has coefficient 1/n! at odd indices and zero at even indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("eCoeff_sinh", "The normalized odd Taylor coefficients", All("n", Nat(),
                Equal(App(Qualified("IntegralEGFComposition", "eCoeff"), Call("sinh"), N()),
                    If(Call("Even", N()), D(0), D(1)))),
                "Factorial normalization cancels the Taylor denominator. Every even index gives zero and every odd index gives one; this coefficient identity also determines the sign of sinh under substitution of -X.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a", "Factorial-scaled coefficients", All("n", Nat(), Equal(A(N()),
                Mul(Cast(App(Qualified("Nat", "factorial"), N()), Rat()), App(Qualified("PowerSeries", "coeff"), N(),
                    Mul(Call("cosh"), Inv(Sub(D(1), Mul(D(2), Call("sinh"))))))))),
                "OEIS A364822, Name (unpaginated): \"Expansion of e.g.f. cosh(x) / (1 - 2*sinh(x)).\" Thus a(n) is n! times the nth ordinary coefficient; the initial index is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("claim", "The conjecture", Iffn(Call("claim"), ClaimBody()),
                "OEIS A364822, Comments (unpaginated): \"Conjectures: For p prime (p > 2), a(p) == 2 (mod p).\" The prime p is natural, z is integer, and z equals a(p) after the rational cast. The strict bound excludes p=2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("num_cast", "Every coefficient is an integer", All("n", Nat(),
                Equal(Cast(Numerator(N()), Rat()), A(N()))),
                "Substituting 2 sinh into the geometric series preserves integral factorial-scaled coefficients. The binomial product formula then proves integrality after multiplication by cosh. The rational numerator therefore equals the rational coefficient after casting.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("num_recurrence", "The integer binomial recurrence", All("n", Nat(),
                Equal(Numerator(N()), Add(If(Call("Even", N()), D(1), D(0)),
                    Mul(D(2), SumBody())))),
                "Multiplication by 1-2 sinh gives the recurrence. The k=n endpoint summand vanishes because sinh has constant coefficient zero. This recurrence also proves the congruence at powers of two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("result", "Residue two at every odd prime", ClaimBody(),
                "At a prime p>2 the even Taylor coefficient is zero. Every interior binomial coefficient is divisible by p; only the constant-index term survives and contributes two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source()),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("tebni364822-cong"), ResolutionKind.Proved))),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Residue/IntegralEGFComposition"))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("tebni364822-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Named(name) : App(Named(name), args);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N() => F.Id("n");
    private static Formula A(Formula n) => Call("a", n);
    private static Formula Numerator(Formula n) => App(Qualified("Rat", "num"), A(n));
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula All(string x, Formula type, Formula body) => Seq(Forall, Sp, F.Id(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Land, Sp, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Implies, Sp, Parenthesized(y));
    private static Formula Iffn(Formula x, Formula y) => Seq(x, Sp, Iff, Sp, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Parenthesized(x), FormulaBinaryOperator.Multiply, Parenthesized(y));
    private static Formula Inv(Formula x) => new Formula.Power(Parenthesized(x), Seq(Minus, D(1)));
    private static Formula If(Formula test, Formula yes, Formula no) => Parenthesized(Seq(Named("if"), Sp,
        Parenthesized(test), Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no));
    private static Formula Taylor(bool even)
    {
        var reciprocal = Inv(Cast(App(Qualified("Nat", "factorial"), N()), Rat()));
        return App(Qualified("PowerSeries", "mk"), Parenthesized(Seq(N(), Colon, Sp, Nat(), Sp, Mapsto, Sp,
            If(Call("Even", N()), even ? reciprocal : D(0), even ? D(0) : reciprocal))));
    }
    private static Formula ClaimBody()
    {
        var p = F.Id("p"); var z = F.Id("z");
        return All("p", Nat(), Imp(App(Qualified("Nat", "Prime"), p),
            Imp(Seq(D(2), Sp, Lt, Sp, p), Seq(Exists, Sp, z, Colon, Sp, Ints(), Comma, Sp,
                And(Equal(Cast(z, Rat()), A(p)), App(Qualified("Int", "ModEq"), Cast(p, Ints()), z, D(2)))))));
    }
    private static Formula SumBody()
    {
        var k = F.Id("k");
        return Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, App(Qualified("Finset", "range"), N()))), Sp,
            Parenthesized(Mul(Mul(Cast(App(Qualified("Nat", "choose"), N(), k), Ints()), Numerator(k)),
                If(Call("Even", Sub(N(), k)), D(0), D(1)))));
    }
}
