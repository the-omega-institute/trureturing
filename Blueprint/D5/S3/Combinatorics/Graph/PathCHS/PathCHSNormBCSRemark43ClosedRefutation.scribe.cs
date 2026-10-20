using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PathCHS;

internal sealed class PathCHSNormBCSRemark43ClosedRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/bouthatchavezsheng2026graphinequalities");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete homogeneous symmetric functions of finite path spectra.",
        H("PathCHSNormBCSRemark43ClosedRefutation"),
        Blocks(
            Node("claim", "The proposed one-term formula", ClaimFormula(), "claim", "Page 18, Remark 4.3: “In particular, if n+1 ≥ d/2, the sum becomes ‖P_n‖_{X,d}^d = ((n² + n − d)/((n + d)(n + d + 1))) binom(n+d+1, d/2).” The hypotheses also require n ≥ 1 and even d ≥ 2. Nat.div is natural-number quotient, exact here because d is even.", DescribeRole.Definition, true),
            Node("result", "A boundary counterexample", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))), "result", "For n=2 and d=6 the complete homogeneous symmetric value is one, while the proposed expression is zero.", DescribeRole.Theorem, false, new OpenProblemResolutionClaim(ProblemSlugRef.Create("bouthat-chavez-sheng-2026-path-chs-remark43-closed-refutation"), ResolutionKind.Refuted))),
        []));
    private static DocumentBlock Node(string id, string title, Formula formula, string name, string prose, DescribeRole role, bool literature, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("pathchsnormbcsremark43closedrefutation-" + id), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
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
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals(string[] names, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--) body = All(names[i], Nat(), body);
        return body;
    }

    private static Formula ClaimBody()
    {
        Formula n = V("n"), d = V("d");
        var nr = Cast(n, Real()); var dr = Cast(d, Real());
        var value = M(Rat(S(A(Pow(nr, D(2)), nr), dr), M(A(nr, dr), A(A(nr, dr), D(1)))), Cast(C("Nat.choose", A(A(n, d), D(1)), C("Nat.div", d, D(2))), Real()));
        return Naturals(["n", "d"], Imp(Le(D(1), n), Imp(Le(D(2), d), Imp(C("Even", d), Imp(Le(C("Nat.div", d, D(2)), A(n, D(1))),
            Eq(C("D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chs", n, d), value))))));
    }
    private static Formula ClaimFormula() => Disp(Eq(N("claim"), ClaimBody()));

}
