using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class KarpRisingFactorialHurwitzRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/karp2012toeplitz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive shifts need not preserve rising-factorial Toeplitz Hurwitz stability.",
        H("Karp's general-shift Hurwitz conjecture fails"), Blocks(
            Paragraph(Text("Local names belong to D5.S3.Analytic.SeriesInequalities.KarpRisingFactorialHurwitzRefutation. "
                + "The rising factorial is ascPochhammer. The function f is real-valued and only its indices zero through n enter Q. "
                + "Subtraction between natural indices, including n−k, k−1, k−10 and 10−k, is truncated subtraction.")),
            Describe.Lean(DescribeId.Create("toeplitz-polynomial"), DeclarationHandle.Create(Prefix + "Q"),
                H("The rising-factorial Toeplitz polynomial"), StatementSource.FromAuthor(Disp(QFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("Equation (3), p. 2 defines the finite sum displayed above.")),
                    Paragraph(Text("Real coefficients and shifts are embedded into the complex numbers by the displayed casts. "
                        + "Polynomial composition substitutes X plus the shift into each rising factorial. "
                        + "The term with index k has the factor f(k)f(n−k) times Nat.choose n k."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hurwitz-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 2 with its standing assumptions"), StatementSource.FromAuthor(Disp(
                    Equal(Local("claim"), Parenthesized(ClaimBody())))), AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("Conjecture 2, p. 2: “If "),
                        Math(Seq(X("f"), Underscore, Grp(X("k")), Caret, Grp(D(2)), Gt,
                            X("f"), Underscore, Grp(Sub(X("k"), D(1))), Sp,
                            X("f"), Underscore, Grp(Add(X("k"), D(1))))),
                        Text(", k=1,2,…,n−1, n≥3, then "),
                        Math(Seq(X("Q"), Caret, Grp(Alpha, Comma, Beta), Underscore, Grp(X("n")), Parenthesized(X("x")))),
                        Text(" is Hurwitz stable.”")),
                    Paragraph(Text("“Recall that a polynomial is called Hurwitz stable if all its zeros have negative real part.” "
                        + "The positive shifts are α and β. The input is nonnegative and nonzero, and the source's zero condition "
                        + "applies only at N>0: a zero there forces all subsequent entries through n to vanish. "
                        + "Strict log-concavity is imposed for 1≤k<n. No total-positivity or unit-shift hypothesis is added."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hurwitz-refutation"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of general-shift Hurwitz stability"), StatementSource.FromAuthor(Disp(
                    Seq(Neg, Sp, Parenthesized(ClaimBody())))), AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Take n=20, α=β=1/t and f(k)=t^((k−10)²+(10−k)²), where 0<t<1. "
                        + "Every input is strictly positive, and the adjacent exponent sum exceeds twice the central exponent by two. "
                        + "Thus the inputs are strictly log-concave.")),
                    Paragraph(Text("Multiplying Q evaluated at z/t by t²⁰ gives a polynomial whose value and derivative depend continuously on t. "
                        + "At t=0 it is 184756 times ((z+1)²⁰−(z(z+2))¹⁰). "
                        + "At z=1/50+(3/4)I the real part of its derivative times the conjugate of its value is strictly negative, by exact rational arithmetic.")),
                    Paragraph(Text("If every root of a complex polynomial has nonpositive real part, its logarithmic derivative has nonnegative real part "
                        + "at every point with positive real part. The root-sum identity proves this sign condition term by term. "
                        + "The strict negative sign persists for some positive t<1, giving a root with positive real part and contradicting the claim. "
                        + "This argument proves existence at n=20; it supplies no explicit finite shift threshold or theorem for every larger degree."))),
                DescribeRole.Theorem)
        )));

    private static Formula QFormula()
    {
        Formula n = X("n"), f = X("f"), k = X("k");
        Formula nk = Sub(n, k);
        Formula asc = Call("ascPochhammer", C(), k);
        Formula ascRest = Call("ascPochhammer", C(), nk);
        Formula coefficient = Call("Polynomial", "C", Mul(Mul(Typed(App(f, k), C()), Typed(App(f, nk), C())),
            Typed(Call("Nat", "choose", n, k), C())));
        Formula shifted(Formula polynomial, Formula shift) => Call("Polynomial", "comp", polynomial,
            Add(Qualified("Polynomial", "X"), Call("Polynomial", "C", Typed(shift, C()))));
        Formula brackets = Sub(Mul(shifted(asc, Alpha), shifted(ascRest, Beta)),
            Mul(shifted(asc, Typed(Add(Alpha, Beta), R())), ascRest));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Seq(k, InMacro, Sp, Call("Finset", "range", Add(n, D(1))))), Sp,
            Mul(coefficient, Parenthesized(brackets)));
        return All(n, N(), All(f, Seq(N(), To, Sp, R()), All(Alpha, R(), All(Beta, R(),
            Equal(App(Local("Q"), n, f, Alpha, Beta), sum)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = X("n"), f = X("f"), k = X("k"), bigN = X("N"), z = X("z");
        Formula fk = App(f, k);
        Formula nonnegative = All(k, N(), Implies(LE(k, n), LE(D(0), fk)));
        Formula nonzero = Ex(k, N(), And(LE(k, n), NE(fk, D(0))));
        Formula noZeros = All(bigN, N(), Implies(Less(D(0), bigN), Implies(LE(bigN, n),
            Implies(Equal(App(f, bigN), D(0)), All(k, N(), Implies(LE(bigN, k),
                Implies(LE(k, n), Equal(fk, D(0)))))))));
        Formula strict = All(k, N(), Implies(LE(D(1), k), Implies(Less(k, n),
            Less(Mul(App(f, Sub(k, D(1))), App(f, Add(k, D(1)))), new Formula.Power(fk, D(2))))));
        Formula stable = All(z, C(), Implies(Equal(Call("Polynomial", "eval", z,
            App(Local("Q"), n, f, Alpha, Beta)), D(0)), Less(Call("Complex", "re", z), D(0))));
        return All(n, N(), All(Alpha, R(), All(Beta, R(), All(f, Seq(N(), To, Sp, R()),
            Implies(LE(D(3), n), Implies(Less(D(0), Alpha), Implies(Less(D(0), Beta),
                Implies(nonnegative, Implies(nonzero, Implies(noZeros, Implies(strict, stable)))))))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula R() => Seq(Mathbb, Grp(X("R")));
    private static Formula C() => Seq(Mathbb, Grp(X("C")));
    private static Formula Local(string name) => Qualified("KarpRisingFactorialHurwitzRefutation", name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Qualified(name), arguments);
    private static Formula Call(string owner, string name, params Formula[] arguments) => App(Qualified(owner, name), arguments);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
