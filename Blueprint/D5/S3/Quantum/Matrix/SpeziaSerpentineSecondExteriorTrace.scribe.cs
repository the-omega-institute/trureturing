using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SpeziaSerpentineSecondExteriorTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/spezia2018a322844");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second exterior trace of the serpentine matrix has Spezia’s magnitude.",
        H("Spezia’s second exterior trace"), Blocks(
            Entry("exterior-trace", "traceExt", "Signed characteristic coefficient",
                TraceDefinition(),
                "The exterior trace is the signed characteristic coefficient when k ≤ n and zero when k > n. "
                    + "Natural subtraction in the coefficient index is truncated. R is any commutative ring.",
                AssessedProvenance.FromRepo(Source)),
            Entry("matrix", "M", "The integer serpentine matrix",
                MatrixDefinition(),
                "A322844 COMMENTS, revision 68, unpaginated: “For n > 1, a(n) is the absolute value of the trace of the 2nd exterior power of an n X n square matrix M(n) defined as M[i,j,n] = j + n*(i-1) if i is odd and M[i,j,n] = n*i - j + 1 if i is even (see A317614). Equivalently, a(n) is the absolute value of the coefficient of the term [x^(n-2)] in the characteristic polynomial of the matrix M(n), or the absolute value of the sum of all principal minors of M(n) of size 2.” The source indices are val(i)+1 and val(j)+1; all entries are integers.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("sequence", "a", "The sequence value",
                All("n", Nat(), Eq(Call("a", V("n")), SequenceBody(V("n")))),
                "A322844 FORMULA, revision 68, unpaginated: “a(n) = (1/12)*n^2*(3*(1 + n^2) - 2*(2 + n^2)*(n mod 2)).” "
                    + "The expression is evaluated in the rationals, and Nat.mod is natural remainder.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("claim", "claim", "Spezia’s first conjecture",
                Iff(V("claim"), Parenthesized(ClaimBody())),
                "A322844 COMMENTS, revision 68, unpaginated: “For n > 1, a(n) is the absolute value of the trace of the 2nd exterior power of an n X n square matrix M(n) defined as M[i,j,n] = j + n*(i-1) if i is odd and M[i,j,n] = n*i - j + 1 if i is even (see A317614). Equivalently, a(n) is the absolute value of the coefficient of the term [x^(n-2)] in the characteristic polynomial of the matrix M(n), or the absolute value of the sum of all principal minors of M(n) of size 2.” Here n ranges over natural orders, 1 < n is the only guard, and the integer absolute trace is cast to the rationals.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("centered-coordinate", "w", "Centered column coordinate",
                All("n", Nat(), All("i", Nat(), Eq(Call("w", V("n"), V("i")),
                    Sub(Add(Cast(V("i"), Rat()), D(1)), Divide(Add(Cast(V("n"), Rat()), D(1)), D(2)))))),
                "Subtracting the midpoint centers the one-based column coordinate.", AssessedProvenance.FromRepo()),
            Entry("row-coordinate", "u", "Affine row coordinate",
                All("n", Nat(), All("i", Nat(), Eq(Call("u", V("n"), V("i")),
                    Sub(Mul(Cast(V("n"), Rat()), Parenthesized(Add(Cast(V("i"), Rat()), D(1)))),
                        Divide(Sub(Cast(V("n"), Rat()), D(1)), D(2)))))),
                "The row coordinate has slope n and midpoint correction (n−1)/2.", AssessedProvenance.FromRepo()),
            Entry("left-factor", "U", "The n by two factor",
                LeftDefinition(),
                "The two entries in each row are the affine coordinate and the alternating sign, over the rationals.",
                AssessedProvenance.FromRepo()),
            Entry("right-factor", "V", "The two by n factor",
                RightDefinition(),
                "The two entries in each column are one and the centered coordinate, over the rationals.",
                AssessedProvenance.FromRepo()),
            Entry("polynomial-factor", "charpoly_factor", "Reduction to two dimensions",
                All("n", Nat(), Imp(Le(D(2), V("n")), Eq(
                    Call("Matrix.charpoly", Call("Matrix.map", Call("M", V("n")), Call("Int.castRingHom", Rat()))),
                    Mul(Pow(Name("Polynomial.X"), Parenthesized(Sub(V("n"), D(2)))),
                        Call("Matrix.charpoly", Parenthesized(Mul(Call("V", V("n")), Call("U", V("n"))))))))),
                "For n ≥ 2 the rectangular product identity factors the characteristic polynomial into X^(n−2) "
                    + "and the characteristic polynomial of V(n)U(n). It also gives all higher exterior traces.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Entry("result", "result", "The second trace has the stated magnitude",
                ClaimBody(),
                "The second characteristic coefficient is −a(n). The four centered moments evaluate its two by two "
                    + "determinant, and parity gives a(n) ≥ 0. Taking the absolute value proves the formula for every n > 1.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("sp322844-serpentine"), ResolutionKind.Proved) : null);

    private static Formula ClaimBody()
    {
        Formula n = V("n");
        Formula trace = Call("traceExt", D(2), Call("M", n));
        Formula value = Parenthesized(Seq(Call("Int.cast", Call("abs", trace)), Colon, Sp, Rat()));
        return All("n", Nat(), Imp(Lt(D(1), n), Eq(value, Call("a", n))));
    }
    private static Formula TraceDefinition()
    {
        Formula n = V("n"), k = V("k"), matrix = V("A"), ring = V("R");
        Formula coefficient = Call("Polynomial.coeff", Call("Matrix.charpoly", matrix), Sub(n, k));
        Formula value = If(Le(k, n), Mul(Pow(Parenthesized(Negative(D(1))), k), coefficient), D(0));
        Formula body = All("n", Nat(), All("k", Nat(), All("A", MatrixType(n, n, ring),
            Eq(Call("traceExt", k, matrix), value))));
        return All("R", Name("Type"), Seq(OpenBracket, Call("CommRing", ring), CloseBracket, Sp, body));
    }
    private static Formula MatrixDefinition()
    {
        Formula n = V("n"), i = V("i"), j = V("j");
        Formula sourceI = Add(Cast(Call("val", i), Int()), D(1));
        Formula sourceJ = Add(Cast(Call("val", j), Int()), D(1));
        Formula odd = Call("Odd", Add(Call("val", i), D(1)));
        Formula forward = Add(sourceJ, Mul(Cast(n, Int()), Parenthesized(Sub(sourceI, D(1)))));
        Formula backward = Add(Sub(Mul(Cast(n, Int()), Parenthesized(sourceI)), Parenthesized(sourceJ)), D(1));
        Formula entries = Fun("i", Call("Fin", n), Fun("j", Call("Fin", n), If(odd, forward, backward)));
        return All("n", Nat(), Eq(Call("M", n), entries));
    }
    private static Formula LeftDefinition()
    {
        Formula n = V("n"), i = V("i"), j = V("j");
        Formula value = If(Eq(j, D(0)), Call("u", n, Call("val", i)),
            Pow(Parenthesized(Negative(D(1))), Call("val", i)));
        return All("n", Nat(), Eq(Call("U", n), Fun("i", Call("Fin", n), Fun("j", Call("Fin", D(2)), value))));
    }
    private static Formula RightDefinition()
    {
        Formula n = V("n"), i = V("i"), j = V("j");
        Formula value = If(Eq(i, D(0)), D(1), Call("w", n, Call("val", j)));
        return All("n", Nat(), Eq(Call("V", n), Fun("i", Call("Fin", D(2)), Fun("j", Call("Fin", n), value))));
    }
    private static Formula SequenceBody(Formula n)
    {
        Formula q = Cast(n, Rat()), square = Pow(q, D(2));
        return Mul(Mul(Divide(D(1), D(1, 2)), square), Parenthesized(Sub(
            Mul(D(3), Parenthesized(Add(D(1), square))),
            Mul(Mul(D(2), Parenthesized(Add(D(2), square))), Cast(Call("Nat.mod", n, D(2)), Rat())))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula MatrixType(Formula m, Formula n, Formula r) => Call("Matrix", Call("Fin", m), Call("Fin", n), r);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Name(string name) => Seq(Operatorname, Grp(Seq(name.Split('.').Select((part, index) =>
        index == 0 ? V(part) : Seq(Dot, V(part))).ToArray())));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) => Parenthesized(Seq(V("fun"), Sp,
        Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(Call("Nat.cast", x), Colon, Sp, type));
    private static Formula If(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(
        Name("if"), Sp, condition, Sp, Name("then"), Sp, yes, Sp, Name("else"), Sp, no));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negative(Formula a) => Seq(Minus, a);
}
