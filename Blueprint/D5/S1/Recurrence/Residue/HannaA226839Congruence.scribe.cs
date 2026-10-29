using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaA226839CongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/HannaA226839Congruence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2013a226839");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every factorial-normalized coefficient of Hanna's original triangular-exponent EGF is an integer congruent to one modulo three.",
        H("Hanna's A226839 Congruence"),
        Blocks(
            Paragraph(Text("All power series are formal over the rationals. Natural division and subtraction "
                + "are used in triangular and innerIntegral. The notation val denotes the integer-to-rational "
                + "cast, natval the natural-to-rational cast, and coeff(n,f) the coefficient of degree n. "
                + "The source defines H(X)=sum over m>=1 of X^(m*(m+1)/2)/m! and A=exp(H). "
                + "No analytic convergence hypothesis or integral representation is assumed.")),
            Node("triangular", "The literal source exponent",
                Disp(Seq(Bound("m", Naturals()), Eqn(Call("triangular", F.Id("m")),
                    new Formula.Floor(new Formula.Fraction(
                        Mul(F.Id("m"), Par(Add(F.Id("m"), D(1)))), D(2)))))),
                "The floor expresses Lean's natural-number division of m*(m+1) by two.",
                DescribeRole.Definition),
            Node("H", "The original inner series",
                Disp(Eqn(Named("H"), App(Qualified("PowerSeries", "mk"),
                    Seq(F.Id("n"), Mapsto, Sp, Call("finsum",
                        Seq(Par(Seq(F.Id("m"), Colon, Naturals())), Mapsto, Sp,
                            Call("ite", Rel(D(0), FormulaRelationOperator.LessThan, F.Id("m")),
                                Call("coeff", F.Id("n"), Call("monomial",
                                    Call("triangular", F.Id("m")),
                                    new Formula.Fraction(D(1), Call("natval", Fact(F.Id("m")))))),
                                D(0)))))))),
                "This is the literal coefficientwise sum over all natural m with the guard 0<m. "
                + "The private coeff_H proof bounds the degree-n support by m<=n, so finsum "
                + "agrees with the original unbounded positive-index formal sum.",
                DescribeRole.Definition),
            Node("A", "The formal exponential",
                Disp(Eqn(Named("A"), App(Qualified("PowerSeries", "subst"),
                    App(Qualified("PowerSeries", "exp"), Rationals()), Named("H")))),
                "Substitution of H into the rational exponential series represents exp(H). "
                + "The proof establishes constantCoeff(H)=0 before using the substitution theorem.",
                DescribeRole.Definition),
            Node("innerIntegral", "The derived integral inner coefficients",
                Disp(Seq(Bound("n", Naturals()), Eqn(Call("innerIntegral", F.Id("n")),
                    Seq(Sum, Underscore, Grp(Seq(F.Id("m"), Eq, D(0))), Caret, Grp(F.Id("n")), Sp,
                        Call("ite", new Formula.Logic(
                            Rel(D(0), FormulaRelationOperator.LessThan, F.Id("m")),
                            FormulaLogicOperator.And,
                            Eqn(Call("triangular", F.Id("m")), F.Id("n"))),
                            App(Qualified("Nat", "ascFactorial"), Add(F.Id("m"), D(1)),
                                new Formula.Binary(F.Id("n"), FormulaBinaryOperator.Subtract, F.Id("m"))),
                            D(0)))))),
                "This natural-valued finite sum is defined over range(n+1). Nat.ascFactorial(m+1,n-m) "
                + "is the rising factorial with n-m factors, with natural truncated subtraction. "
                + "At triangular(m)=n it equals n!/m!. The private eCoeff_H proves that this "
                + "sum, cast to the rationals, equals n! times coeff(n,H); this equality is derived.",
                DescribeRole.Definition),
            Node("result", "The congruence at every nonnegative index",
                Disp(Seq(Bound("n", Naturals()), Exists, Sp, F.Id("k"), Colon, Integers(), Comma, Sp,
                    Eqn(Mul(Call("natval", Fact(F.Id("n"))), Call("coeff", F.Id("n"), Named("A"))),
                        Add(D(1), Mul(D(3), Call("val", F.Id("k"))))))),
                "The literal source conjecture is: a(n) == 1 (mod 3) (conjecture - valid up to "
                + "n=1024; if true for n>=0, why?). The integer witness proves integrality and "
                + "the residue simultaneously, for every natural n including zero. For m=2 "
                + "the factorial ratio is three; for m>=3 it contains at least three consecutive "
                + "factors and is divisible by three. The integral inner coefficients therefore "
                + "reduce to the identity series. Existing IntegralEGFComposition.eCoeff_composition "
                + "and composition_map, followed by the original private composition_identity_right "
                + "from QuarticEGFModFour, give the conclusion. Only integers are reduced to "
                + "ZMod(3); there is no rational-to-residue-field homomorphism. "
                + "The source's finite-check report supplies no universal proof. "
                + "The proof is derived in this repository; bounded literature nonhits certify no priority.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("hanna-a226839-" + (name == "A" ? "outer" : name == "H" ? "inner" : name.ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Call(string name, params Formula[] xs) => App(Named(name), xs);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Fact(Formula f) => Seq(f, Bang);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Bound(string name, Formula type) => Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp);
    private static Formula Eqn(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
}
