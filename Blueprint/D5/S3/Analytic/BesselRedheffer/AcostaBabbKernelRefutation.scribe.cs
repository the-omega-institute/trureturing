using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRedheffer;

internal sealed class AcostaBabbKernelRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/acostababb2024partial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-mode counterexample to weighted Bessel-kernel positivity.",
        H("The explicit weighted Bessel kernel"), Blocks(
            Node("j", "Successive positive zeros", DescribeRole.Definition,
                Aligned(Equal(Call("j", D(0)), D(0)),
                    Equal(Call("j", D(1)), Call("firstZero", D(0))),
                    All(X("n"), Nat(), Equal(Call("j", Add(X("n"), D(2))),
                        Call("sInf", Seq(OpenBrace, X("x"), Colon, Sp, Real(), Sp, Bar, Sp,
                            And(Less(D(0), X("x")),
                                And(Less(Call("j", Add(X("n"), D(1))), X("x")),
                                    Equal(Call("nbessel", D(0), X("x")), D(0)))), CloseBrace))))),
                AssessedProvenance.FromLiterature(Source),
                Text("Lemma 2.2, p. 6: “Let jₘ denote the mth positive zero of J₀. Then”. The real function nbessel 0 is J₀. The sequence is indexed from one, with an unused value zero at index zero; the first zero is firstZero 0, and later entries are infima of the positive zeros strictly above the preceding entry. Only the first two entries are needed below; their infima are attained and lie in the rational intervals described below.")),
            Node("S", "The printed partial sum", DescribeRole.Definition,
                All(Alpha, Real(), All(X("m"), Nat(), All(X("x"), Real(),
                    Equal(Call("S", Alpha, X("m"), X("x")),
                        SumOver(X("k"), CallQualified("Finset", "Icc", D(1), X("m")),
                            Mul(Pow(Call("j", X("m")), Alpha),
                                Call("nbessel", D(0), Mul(Call("j", X("k")), X("x"))))))))),
                AssessedProvenance.FromLiterature(Source),
                Text("Section 3, p. 7: “Let us write "),
                Math(Equal(SourceS(X("m")), SourceSum(X("k"), X("m"),
                    Seq(SourceJPow(X("m")), Sp, SourceJZero(Seq(SourceJ(X("k")), Sp, X("x"))))))),
                Text(".” The factor is jₘ raised to alpha even inside the sum over k. Consequently this printed S does not give the printed Cesaro equality for the explicit weighted kernel; S is retained separately.")),
            Node("K", "The explicit weighted kernel", DescribeRole.Definition,
                All(Alpha, Real(), All(X("M"), Nat(), All(X("x"), Real(),
                    Equal(Call("K", Alpha, X("M"), X("x")),
                        Seq(X("if"), Sp, Parenthesized(Equal(X("M"), D(0))), Sp,
                            X("then"), Sp, D(1), Sp, X("else"), Sp,
                            SumOver(X("m"), CallQualified("Finset", "Icc", D(1), X("M")),
                                Mul(Mul(Parenthesized(Sub(D(1),
                                            new Formula.Fraction(Parenthesized(Typed(X("m"), Real())),
                                                Add(Parenthesized(Typed(X("M"), Real())), D(1))))),
                                        Pow(Call("j", X("m")), Alpha)),
                                    Call("nbessel", D(0), Mul(Call("j", X("m")), X("x")))))))))),
                AssessedProvenance.FromLiterature(Source),
                Text("Section 3, p. 7, the explicit right-hand display is “"),
                Math(Seq(Eq, Sp, SourceSum(X("m"), X("M"),
                    Seq(Parenthesized(Sub(D(1), new Formula.Fraction(X("m"), Add(X("M"), D(1))))), Sp,
                        SourceJPow(X("m")), Sp, SourceJZero(Seq(SourceJ(X("m")), Sp, X("x"))))))),
                Text(".” The separate sentence is “We will also set "),
                Math(Seq(SourceKernel(D(0)), Sp, Equiv, Sp, D(1))), Text(" when "),
                Math(Equal(X("M"), D(0))),
                Text(".” Here the sum ranges over positive natural indices, and both m and M are cast to real numbers in the weight. K uses this explicit formula, independently of the preceding printed S equality.")),
            Node("claim", "Conjecture 1", DescribeRole.Definition,
                Equal(X("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                Text("Conjecture 1, p. 10: “For all, "),
                Math(Seq(D(0), Sp, F.Leq, Sp, Alpha, Sp, F.Leq, Sp, new Formula.Fraction(D(1), D(2)))),
                Text(", "), Math(Seq(X("M"), Sp, InMacro, Sp, Nat())), Text(" and "),
                Math(Seq(X("x"), Sp, InMacro, Sp, OpenBracket, D(0), Comma, D(1), CloseBracket)),
                Text(", "), Math(Seq(SourceKernel(X("M")), Sp, Geq, Sp, D(0))),
                Text(".” The natural M includes zero; alpha and x are real numbers, and both intervals are closed. K is the explicit weighted formula on p. 7.")),
            Node("result", "Refutation at two modes", DescribeRole.Theorem,
                Seq(Neg, Sp, Parenthesized(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Text("At alpha=1/2, M=2 and x=999/1000 the weighted kernel is strictly negative. If a=j 1 and b=j 2, then 24048255/10000000 <= a <= 24048256/10000000 and 55200781/10000000 <= b <= 55200782/10000000. Alternating-series estimates give nbessel 0 (a*x) <= 1/800 and nbessel 0 (b*x) <= -187/100000; also sqrt(a) <= 1551/1000 and sqrt(b) >= 2349/1000. Thus the negative second mode outweighs twice the first mode. The first two zeros are isolated by derivative signs, the intermediate value theorem and a negative polynomial bound between the two intervals. This proves the single counterexample. A uniform rectangle of negative values, a sharp exponent threshold, positivity at other mode counts, and the source's downstream existence assertions are separate questions.")))));

    private static DocumentBlock Node(string name, string title, DescribeRole role,
        Formula formula, AssessedProvenance provenance, params Inline[] prose) => Describe.Lean(
            DescribeId.Create("acosta-babb-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(prose)), role);
    private static Formula SourceJ(Formula m) => new Formula.Subscript(X("j"), m);
    private static Formula SourceJPow(Formula m) => Seq(X("j"), Underscore, Grp(m), Caret, Grp(Alpha));
    private static Formula SourceJZero(Formula z) =>
        Seq(X("J"), Underscore, Grp(D(0)), Parenthesized(z));
    private static Formula SourceS(Formula m) =>
        Seq(X("S"), Caret, Grp(Alpha), Underscore, Grp(m), Parenthesized(X("x")));
    private static Formula SourceKernel(Formula m) =>
        Seq(X("K"), Caret, Grp(Alpha), Underscore, Grp(m), Parenthesized(X("x")));
    private static Formula SourceSum(Formula k, Formula m, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(k, Eq, D(1))), Caret, Grp(m), Sp, body);
    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Aligned(params Formula[] rows) => new Formula.Aligned([.. rows]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula CallQualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name)))), [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Typed(variable, type)), Comma, Sp, body);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula SumOver(Formula variable, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(variable, Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula ClaimBody()
    {
        var conclusion = Leq(D(0), Call("K", Alpha, X("M"), X("x")));
        var point = All(X("x"), Real(), Imp(Leq(D(0), X("x")),
            Imp(Leq(X("x"), D(1)), conclusion)));
        return All(Alpha, Real(), Imp(Leq(D(0), Alpha),
            Imp(Leq(Alpha, new Formula.Fraction(D(1), D(2))), All(X("M"), Nat(), point))));
    }
}
