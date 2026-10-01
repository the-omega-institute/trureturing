using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HoneycombTrapeziumHuckelDeterminantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/molinari2022graphene");
    private const string ConjectureSentence =
        "The determinant of the Hückel matrix Hₖ,ₙ(𝐱, 𝐲) of a honeycomb trapezium with rows with 2k+1, 2k+3, ... , 2n+1 sites, size (n+1)²−k², is equal to the determinant of the following matrix of size n+1−k";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant of a honeycomb trapezium's Hückel matrix equals the determinant of Molinari's reduced Pascal matrix, for arbitrary boundary weights in any commutative ring.",
        H("Honeycomb trapezia and reduced Pascal determinants"),
        Blocks(
            Node("sourceT", "The horizontal blocks", SourceTFormula(),
                "Molinari, arXiv:2206.14428v2, page 4: “A block Tₘ(xₘ,yₘ) is a square matrix of size 2m+1 that describes a row of 2m+1 atoms with boundary parameters xₘ,yₘ:”. The displayed T_0 is x_0+y_0; for positive m, T_m has unit entries at adjacent sites, y_m at (0,2m), and x_m at (2m,0). sourceT gives exactly these entries. Its natural-number arguments i,j are restricted to Fin(2m+1) when used as a block. Cases are read in the displayed order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sourceR", "The vertical blocks", SourceRFormula(),
                "Molinari, page 4: “The blocks Rₘ are (2m+1)×(2m−1), with unit elements for the vertical edges in the graph, joining atoms in rows m−1 and m:”. The displayed R_1, R_2 and R_3 put ones exactly at (2j+1,2j). sourceR is this entry rule; the block dimensions restrict its natural arguments. The operator mod is natural-number remainder.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sourceTriangle", "The triangle matrix", TriangleFormula(),
                "The source block tridiagonal matrix has T_m on its diagonal, R_m below the diagonal, and R_m transposed above it (page 4). Its dependent index type is Sigma m : Fin(n+1-k), Fin(2(val(m)+k)+1). An element a has first coordinate a.fst, second coordinate a.snd, and val extracts a Fin coordinate's natural value. At k=0 this retains the source's row order and within-row site order. All formulas use a commutative ring R and functions x,y : N to R. Natural subtraction truncates at zero; finite-type parameters have that same convention. The triangle entry formula includes every zero block.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("huckel", "The trapezium matrix", HuckelFormula(),
                "Molinari, page 9: “If rows 0,1,...,k−1 are removed from a honeycomb triangle, a trapezium results, with rows of lengths 2k+1, ... , 2n+1. The corresponding Hückel matrix Hₖ,ₙ(𝐱,𝐲) is obtained by deleting the first k² rows and columns of Hₙ(𝐱,𝐲). Its size is (n+1)²−k²=(2k+1) + ... + (2n+1).” The retained index adds k to the row coordinate and keeps the site coordinate. The entry formula is the principal submatrix along this retained index, so it deletes precisely the first 1+3+...+(2k−1)=k² sites. The notation mk means Fin.mk; its membership inequalities are exactly those forced by the source and retained index types. For k<=n there are the rows k through n, including their boundary weights.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reducedPascal", "The displayed reduced Pascal matrix", PascalFormula(),
                "This is the matrix displayed after Conjecture 2 on page 9. Its indices i,j run through Fin(n+1-k); index i labels source row n-val(i), so rows and columns run from n down to k. The two-line parenthesized symbols are binomial coefficients Nat.choose, mapped to R by its natural-number homomorphism. The upper entries have alternating signs multiplying y; the lower entries have positive binomial coefficients multiplying x. Cases use Fin equality on the diagonal and natural values for the strict order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 2", ClaimFormula(),
                "Molinari, arXiv:2206.14428v2, section 5, page 9, Conjecture 2, verbatim: “" + ConjectureSentence + ":”. The displayed matrix is reducedPascal. The encoding quantifies over every commutative ring R, every k,n in N with k<=n, and arbitrary functions x,y : N to R. The source's real and complex boundary parameters are specializations. At k=0 this gives the triangle identity in Conjecture 1; the assertion here is Conjecture 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Equality of the determinants", Disp(F.Id("claim")),
                "Molinari's Conjecture 2 (the claim) holds. Separate even and odd sites in each row. Apart from the boundary weights, edges join different colours, giving a matrix with blocks X, B transposed, B and zero. The lift U at blue site (m,j), in row l, is (-1)^j times the binomial coefficient C(j,m-l) when l<=m, and zero otherwise. Pascal's recurrence gives BU=0, and the left endpoints give the identity. The restriction of B to the other blue sites is lower triangular with diagonal one. A change of blue coordinates and a Schur complement therefore give det(H)=(-1)^q det(U transposed X U), with q the number of red sites. The right endpoints of U give W_ml=(-1)^m C(m,l), hence U transposed X U=diag(y)W+W transposed diag(x). Multiplying columns by (-1)^l and then reversing the rows and the columns simultaneously gives reducedPascal; the column-sign determinant is (-1)^q and cancels the earlier sign. Every step takes place over an arbitrary commutative ring. The paper supplies the conjecture; the proof is repository-produced.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("molinari-2022-honeycomb-trapezium-huckel-determinant"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("molinari-honeycomb-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula All(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula First(Formula a) => Call("fst", a);
    private static Formula Second(Formula a) => Call("snd", a);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Sites(Formula k, Formula n) => Parenthesized(Seq(Sigma, Sp, F.Id("m"), Colon, Sp, Fin(Sub(Add(n, D(1)), k)), Comma, Sp, Fin(Add(Mul(D(2), Parenthesized(Add(Val(F.Id("m")), k))), D(1)))));
    private static Formula Weights(Formula r) => new Formula.TypeArrow(Nats(), r);
    private static Formula Ring(Formula body) => All("R", Named("Type"), Implies(Call("CommRing", F.Id("R")), body));
    private static Formula XY(Formula body) => All("x", Weights(F.Id("R")), All("y", Weights(F.Id("R")), body));
    private static Formula CaseRow(Formula value, Formula condition) => Seq(value, Sp, Amp, Sp, condition);
    private static Formula Cases(params Formula[] rows)
    {
        var items = new System.Collections.Generic.List<Formula> { Begin, Grp(F.Id("cases")) };
        for (var i = 0; i < rows.Length; ++i)
        {
            if (i > 0) items.Add(RowBreak);
            items.Add(rows[i]);
        }
        items.Add(End); items.Add(Grp(F.Id("cases")));
        return Seq([.. items]);
    }
    private static Formula Binomial(Formula upper, Formula lower) =>
        Seq(Begin, Grp(F.Id("pmatrix")), upper, RowBreak, lower, End, Grp(F.Id("pmatrix")));

    private static Formula SourceTFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), m = F.Id("m"), i = F.Id("i"), j = F.Id("j");
        var value = Cases(
            CaseRow(Add(Call("x", D(0)), Call("y", D(0))), Equal(m, D(0))),
            CaseRow(D(1), Or(Equal(Add(i, D(1)), j), Equal(Add(j, D(1)), i))),
            CaseRow(Call("y", m), And(Equal(i, D(0)), Equal(j, Mul(D(2), m)))),
            CaseRow(Call("x", m), And(Equal(i, Mul(D(2), m)), Equal(j, D(0)))),
            CaseRow(D(0), Named("otherwise")));
        return Disp(Ring(XY(All("m", Nats(), All("i", Nats(), All("j", Nats(),
            Equal(Call("sourceT", x, y, m, i, j), value)))))));
    }

    private static Formula SourceRFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return Disp(Ring(All("i", Nats(), All("j", Nats(), Equal(Call("sourceR", i, j), Cases(
            CaseRow(D(1), And(Equal(Call("mod", i, D(2)), D(1)), Equal(i, Add(j, D(1))))),
            CaseRow(D(0), Named("otherwise"))))))));
    }

    private static Formula TriangleFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a"), b = F.Id("b"), x = F.Id("x"), y = F.Id("y");
        var m = Val(First(a)); var t = Val(First(b)); var i = Val(Second(a)); var j = Val(Second(b));
        var value = Cases(
            CaseRow(Call("sourceT", x, y, m, i, j), Equal(First(a), First(b))),
            CaseRow(Call("sourceR", i, j), Equal(m, Add(t, D(1)))),
            CaseRow(Call("sourceR", j, i), Equal(t, Add(m, D(1)))),
            CaseRow(D(0), Named("otherwise")));
        return Disp(Ring(All("n", Nats(), XY(All("a", Sites(D(0), n), All("b", Sites(D(0), n),
            Equal(Call("sourceTriangle", n, x, y, a, b), value)))))));
    }

    private static Formula HuckelFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), a = F.Id("a"), b = F.Id("b"), x = F.Id("x"), y = F.Id("y");
        var entry = Ring(All("k", Nats(), All("n", Nats(), XY(All("a", Sites(k, n), All("b", Sites(k, n),
            Equal(Call("huckel", k, n, x, y, a, b),
                Call("sourceTriangle", n, x, y, RetainedIndex(a, k), RetainedIndex(b, k)))))))));
        return Disp(entry);
    }

    private static Formula RetainedIndex(Formula a, Formula k) =>
        Pair(Call("mk", Add(Val(First(a)), k)), Call("mk", Val(Second(a))));

    private static Formula PascalFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), i = F.Id("i"), j = F.Id("j"), x = F.Id("x"), y = F.Id("y");
        var vi = Val(i); var vj = Val(j); var ni = Sub(n, vi); var nj = Sub(n, vj);
        var size = Fin(Sub(Add(n, D(1)), k));
        var value = Cases(
            CaseRow(Add(Call("x", ni), Call("y", ni)), Equal(i, j)),
            CaseRow(Mul(Mul(new Formula.Power(Parenthesized(new Formula.Negate(D(1))), Sub(vj, vi)),
                Call("cast", Binomial(ni, Sub(vj, vi)))), Call("y", ni)), Less(vi, vj)),
            CaseRow(Mul(Call("cast", Binomial(nj, Sub(vi, vj))), Call("x", nj)), Named("otherwise")));
        return Disp(Ring(All("k", Nats(), All("n", Nats(), XY(All("i", size, All("j", size,
            Equal(Call("reducedPascal", k, n, x, y, i, j), value))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), x = F.Id("x"), y = F.Id("y");
        var identity = Equal(Call("det", Call("huckel", k, n, x, y)),
            Call("det", Call("reducedPascal", k, n, x, y)));
        var quantified = Ring(All("k", Nats(), All("n", Nats(), Implies(Le(k, n), XY(identity)))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(quantified)));
    }
}
