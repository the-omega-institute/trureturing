using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PathCHS;

internal sealed class PathCHSNormBCSRemark43Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/bouthatchavezsheng2026graphinequalities");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete homogeneous symmetric functions of finite path spectra.",
        H("PathCHSNormBCSRemark43"),
        Blocks(
            Node("trig", "The trigonometric expression", TrigFormula(), "trigForm", "Page 18, Remark 4.3: “While we have not been able to prove this fact, we have found that the following appears to hold for all n ≥ 1 and all even d ≥ 2: ‖P_n‖_{X,d}^d = (2^{n+d}/(n+1)) Σ_{k=1}^{n} (−1)^{k+1} cos^{n−1+d}(πk/(n+1)) sin²(πk/(n+1)) = Σ_{j=−∞}^{∞} [binom(n+d−1, (n+1)j + d/2) − binom(n+d−1, (n+1)j + d/2 − 1)].” The index k runs through the natural interval from 1 to n.", DescribeRole.Definition, true),
            Node("bilateral", "The bilateral binomial sum", BilateralFormula(), "bilateralForm", "Page 18, Remark 4.3: “While we have not been able to prove this fact, we have found that the following appears to hold for all n ≥ 1 and all even d ≥ 2: ‖P_n‖_{X,d}^d = (2^{n+d}/(n+1)) Σ_{k=1}^{n} (−1)^{k+1} cos^{n−1+d}(πk/(n+1)) sin²(πk/(n+1)) = Σ_{j=−∞}^{∞} [binom(n+d−1, (n+1)j + d/2) − binom(n+d−1, (n+1)j + d/2 − 1)].” The sum is finsum over integer j; only finitely many terms are nonzero. Nat.div is the natural quotient.", DescribeRole.Definition, true),
            Node("claim", "The two identities of Remark 4.3", ClaimFormula(), "claim", "Page 18, Remark 4.3: “While we have not been able to prove this fact, we have found that the following appears to hold for all n ≥ 1 and all even d ≥ 2: ‖P_n‖_{X,d}^d = (2^{n+d}/(n+1)) Σ_{k=1}^{n} (−1)^{k+1} cos^{n−1+d}(πk/(n+1)) sin²(πk/(n+1)) = Σ_{j=−∞}^{∞} [binom(n+d−1, (n+1)j + d/2) − binom(n+d−1, (n+1)j + d/2 − 1)].” The graph value is the complete homogeneous symmetric polynomial of the path adjacency eigenvalues.", DescribeRole.Definition, true),
            Node("result", "Proof of both identities", Disp(ClaimBody()), "result", "The recurrence identity tⁿ Sₙ(t⁻¹)=cont(t²;1,1;n) for nonzero t identifies the reciprocal product at the Chebyshev nodes. Partial fractions give the sine-square weights. Pairing the positive and negative integer indices gives the finite second-difference formula.", DescribeRole.Theorem, false)),
        []));
    private static DocumentBlock Node(string id, string title, Formula formula, string name, string prose, DescribeRole role, bool literature, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("pathchsnormbcsremark43-" + id), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string name)
    {
        var parts = name.Split('.');
        Formula value = N(parts[0]);
        for (var i = 1; i < parts.Length; i++) value = Seq(value, Dot, N(parts[i]));
        return value;
    }
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(Q(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula A(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula S(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula M(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Rat(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals(string[] names, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--) body = All(names[i], Nat(), body);
        return body;
    }
    private static Formula SumOver(string name, Formula set, Formula body) => Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));

    private static Formula Chs(Formula n, Formula d) => C("D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chs", n, d);
    private static Formula Binom(Formula l, Formula r) => C("D5.S0.Conventions.IntegerIndexBinomial.binom", l, r);
    private static Formula Angle(Formula n, Formula k) => Rat(M(Q("Real.pi"), Cast(k, Real())), A(Cast(n, Real()), D(1)));
    private static Formula TrigFormula()
    {
        Formula n = V("n"), d = V("d"), k = V("k");
        var angle = Angle(n, k);
        var term = M(M(Pow(Cast(new Formula.Negate(D(1)), Real()), A(k, D(1))), Pow(C("Real.cos", angle), A(S(n, D(1)), d))), Pow(C("Real.sin", angle), D(2)));
        return Disp(Naturals(["n", "d"], Eq(C("trigForm", n, d), M(Rat(Pow(Cast(D(2), Real()), A(n, d)), A(Cast(n, Real()), D(1))), SumOver("k", C("Finset.Icc", D(1), n), term)))));
    }
    private static Formula BilateralFormula()
    {
        Formula n = V("n"), d = V("d"), j = V("j");
        var l = S(A(n, d), D(1));
        var r = A(M(A(Cast(n, Int()), D(1)), j), Cast(C("Nat.div", d, D(2)), Int()));
        var term = S(Cast(Binom(l, r), Int()), Cast(Binom(l, S(r, D(1))), Int()));
        var sum = Seq(new Formula.Subscript(new Formula.Power(Sum, N("f")), Seq(j, Colon, Int())), Sp, Parenthesized(term));
        return Disp(Naturals(["n", "d"], Eq(C("bilateralForm", n, d), sum)));
    }
    private static Formula ClaimBody() => Naturals(["n", "d"], Imp(Le(D(1), V("n")), Imp(Le(D(2), V("d")), Imp(C("Even", V("d")),
        And(Eq(Chs(V("n"), V("d")), C("trigForm", V("n"), V("d"))), Eq(Chs(V("n"), V("d")), Cast(C("bilateralForm", V("n"), V("d")), Real())))))));
    private static Formula ClaimFormula() => Disp(Eq(N("claim"), ClaimBody()));

}
