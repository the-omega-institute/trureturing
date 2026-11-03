using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class MouradAbbasC51RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/MouradAbbasC51Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mourad2013spectra");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An infinite family of positive-trace block matrices refutes Mourad–Abbas Conjecture 5.1.",
        H("Mourad–Abbas Conjecture 5.1"),
        Blocks(
            Node("ma-symmetric-polytope", "The full symmetric polytope", "DeltaSymm",
                DeltaFormula(),
                "Page 1: ‘The set of all n×n doubly-stochastic matrices is denoted by Δ_n "
                    + "and the set of all the symmetric elements in Δ_n will be denoted by Δ^s_n.’ "
                    + "The entries are real, indexed by Fin n. doublyStochastic requires "
                    + "nonnegative entries and row and column sums equal to one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ma-trace-slice", "A trace slice", "traceSlice", SliceFormula(),
                "Page 1: ‘For 0≤a≤n, denote by Δ^s_n(a) to be the set of all elements "
                    + "of Δ^s_n with trace a.’ The set expression is defined for every real a; "
                    + "the inequalities on a occur in the conjecture.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ma-c-matrix", "The matrix C", "C", CFormula(),
                "Page 1: ‘The third is C_n which denotes the n×n matrix whose diagonal "
                    + "entries are all zeroes and whose off-diagonal entries are equal to "
                    + "1/(n−1) (here for n≥2).’ Division and subtraction in this formula "
                    + "are real operations; the order n is coerced to ℝ before subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ma-permutation-similarity", "Permutation similarity",
                "IsPermutationallySimilar", PermutationFormula(),
                "Page 2: ‘Two matrices A and B are said to be permutationally similar "
                    + "if B=PᵀAP for some permutation matrix P.’ The permutation acts on Fin n; "
                    + "its real permutation matrix is Equiv.Perm.permMatrix.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ma-spectral-determination", "Determination by spectra", "IsDS", DSFormula(),
                "Page 2: ‘If in addition A is symmetric then A is said to be DS in Δ_n^s "
                    + "if B∈Δ_n^s is similar to A implies that B is permutationally similar "
                    + "to A.’ IsConj is ordinary similarity by an invertible real matrix. "
                    + "B ranges over every real symmetric doubly stochastic matrix of the same order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ma-conjecture", "Conjecture 5.1", "claim",
                Disp(Iff(F.Id("claim"), ClaimBody())),
                "Page 10, Conjecture 5.1: ‘For 0<a≤n, the only elements of Δ_n^s(a) "
                    + "that are DS in Δ_n^s are points on the line segments [I_n,C_n], "
                    + "[I_n,P] and [C_n,P] where P is a vertex of Δ_n^s.’ "
                    + "The word ‘only’ gives the necessary condition displayed here. "
                    + "The identity is the matrix 1, n≥2, all segments are closed, and "
                    + "extremePoints refers to the full symmetric polytope rather than its trace slice.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ma-refutation", "Conjecture 5.1 is false", "result",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "For every k≥4, r≥2 and real 0<t<1/k², take r diagonal blocks of size k "
                    + "with diagonal t and off-diagonal (1−t)/(k−1), and zero entries between "
                    + "blocks. Put λ=(kt−1)/(k−1). For any similar symmetric doubly stochastic "
                    + "matrix B, the matrix (B−λ1)/(1−λ) is a nonnegative stochastic idempotent. "
                    + "A weighted sum of squared row differences shows that positive entries "
                    + "join equal rows. The support-size bound and trace then force equal blocks "
                    + "of size k, giving one permutation that aligns B with the original matrix. "
                    + "A cross-block zero excludes the segment involving C, while a four-cycle "
                    + "perturbation excludes every extreme point on an identity ray. "
                    + "The final contradiction takes k=4, r=2, t=1/40, hence order 8 and trace 1/5. "
                    + "The order-three classification and the two other questions in Section 5 "
                    + "are unaffected; the version restricted to irreducible matrices remains open.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ma2013-dsspectral"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula DeltaFormula()
    {
        var n = F.Id("n");
        var a = F.Id("A");
        return Disp(All("n", N, EqF(Call("DeltaSymm", n),
            SetOf("A", MatrixType(n), And(
                Member(a, Call("doublyStochastic", R, Call("Fin", n))),
                App(Qualified("Matrix", "IsSymm"), a))))));
    }

    private static Formula SliceFormula()
    {
        var n = F.Id("n");
        var t = F.Id("a");
        var a = F.Id("A");
        return Disp(All("n", N, All("a", R,
            EqF(Call("traceSlice", n, t), SetOf("A", MatrixType(n),
                And(Member(a, Call("DeltaSymm", n)),
                    EqF(App(Qualified("Matrix", "trace"), a), t)))))));
    }

    private static Formula CFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var j = F.Id("j");
        return Disp(All("n", N, EqF(Call("C", n),
            Lambda("i", Call("Fin", n), Lambda("j", Call("Fin", n),
                Call("ite", EqF(i, j), D(0), new Formula.Fraction(D(1),
                    Seq(RealCast(n), Minus, D(1)))))))));
    }

    private static Formula PermutationFormula()
    {
        var n = F.Id("n");
        var a = F.Id("A");
        var b = F.Id("B");
        var s = F.Id("s");
        var p = App(Qualified("Equiv", "Perm", "permMatrix"), R, s);
        return Disp(All("n", N, All("A", MatrixType(n), All("B", MatrixType(n),
            Iff(Call("IsPermutationallySimilar", a, b),
                ExistsOne("s", App(Qualified("Equiv", "Perm"), Call("Fin", n)),
                    EqF(b, Mul(Mul(App(Qualified("Matrix", "transpose"), p), a), p))))))));
    }

    private static Formula DSFormula()
    {
        var n = F.Id("n");
        var a = F.Id("A");
        var b = F.Id("B");
        return Disp(All("n", N, All("A", MatrixType(n),
            Iff(Call("IsDS", a), And(Member(a, Call("DeltaSymm", n)),
                All("B", MatrixType(n), Imp(Member(b, Call("DeltaSymm", n)),
                    Imp(Call("IsConj", a, b), Call("IsPermutationallySimilar", a, b)))))))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var a = F.Id("a");
        var m = F.Id("A");
        var p = F.Id("P");
        var identity = Parenthesized(Seq(D(1), Colon, MatrixType(n)));
        var c = Call("C", n);
        var extreme = App(Qualified("Set", "extremePoints"), R, Call("DeltaSymm", n));
        var segments = Or(Member(m, Call("segment", R, identity, c)),
            ExistsOne("P", MatrixType(n), And(Member(p, extreme),
                Or(Member(m, Call("segment", R, identity, p)),
                    Member(m, Call("segment", R, c, p))))));
        return All("n", N, Imp(Le(D(2), n), All("a", R,
            Imp(Less(D(0), a), Imp(Le(a, RealCast(n)), All("A", MatrixType(n),
                Imp(Member(m, Call("traceSlice", n, a)), Imp(Call("IsDS", m), segments))))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Colon, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Call(string name, params Formula[] args) => App(F.Id(name), args);
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Qualified(params string[] names) =>
        Seq(Operatorname, Grp(Seq(names.SelectMany((name, i) => i == 0
            ? new[] { F.Id(name) } : new[] { Dot, F.Id(name) }).ToArray())));
    private static Formula MatrixType(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), R);
    private static Formula RealCast(Formula n) => Parenthesized(Seq(n, Colon, R));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula EqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
}
