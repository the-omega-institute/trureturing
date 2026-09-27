using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class BarryRiordanPascalKernelDeterminantDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/barry2013riordanpascal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barry's Riordan kernel matrix is a Gram product with determinant one.",
        H("Barry's Riordan-Pascal Kernel Determinant"),
        Blocks(
            Paragraph(Text(
                "Let C embed an integer as a constant formal power series and let X be "
                    + "the power-series variable. The inverse invOfUnit(1-C(a)X,1) "
                    + "is the formal power-series interpretation of 1/(1-ax). "
                    + "Polynomial C embeds an integer or a polynomial as a constant "
                    + "polynomial. Fin(n+1) indexes the integers from zero through n.")),
            Node(
                "barry-riordan-array",
                "The generalized Pascal Riordan array",
                "riordan",
                RiordanFormula(),
                "Barry's page-1 pair is g=1/(1-ax) and "
                    + "f=x(1+bx)/(1-ax)^m. Section 2 indexes columns from zero and "
                    + "generates column k by g times f^k. Thus riordan(m,a,b,n,k) "
                    + "is the coefficient of X^n in g times f^k.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "barry-row-polynomial",
                "The row polynomial",
                "P",
                PFormula(),
                "Printed page 19 defines P_n(x;m,a,b) as the sum from k=0 through n "
                    + "of T_(n,k) times x^k. The finite sum here has the same inclusive "
                    + "bounds and uses the Riordan entries as its coefficients.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "barry-truncated-matrix",
                "The finite Riordan matrix",
                "M",
                MFormula(),
                "Printed page 20 defines M_n as the first n+1 rows and columns of M. "
                    + "The preceding sentence fixes m=2 and a=b=1, so both finite "
                    + "indices range over Fin(n+1) and each entry is riordan(2,1,1,i,k).",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "barry-kernel-matrix",
                "The polynomial kernel matrix",
                "Dtilde",
                DtildeFormula(),
                "The bivariate polynomial is represented as a polynomial in x whose "
                    + "coefficients are polynomials in y. The (i,k) entry first extracts "
                    + "the outer x^i coefficient and then the inner y^k coefficient from "
                    + "the sum of P_j(x)P_j(y) for j=0 through n. The page-20 display "
                    + "prints k below the sum while retaining P_j in the summand; the "
                    + "unambiguous comparison display on page 19 uses j as the index.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "barry-conjecture-thirty-two",
                "Conjecture 32",
                "claim",
                ClaimFormula(),
                "The source states: \"Conjecture 32. The matrix D̃_n(2, 1, 1) "
                    + "with generating function Σ_{k=0}^{n} P_j(x; 2, 1, 1)P_j(y; 2, 1, 1) "
                    + "is given by M_n^{(2)}(a, b)^t M_n^{(2)}(a, b). We then have "
                    + "|D̃_n(2, 1, 1)| = 1 for n ≥ 0. In the above the notation "
                    + "M_n denotes the matrix formed from the first (n + 1) rows and "
                    + "columns of M.\" The right side is read at a=b=1 from the sentence "
                    + "immediately preceding the conjecture and from its left side.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "barry-conjecture-thirty-two-proved",
                "Conjecture 32 holds",
                "result",
                ResultFormula(),
                "For each pair of finite indices, coefficient extraction from the kernel "
                    + "sum gives the finite sum of products T_(j,i)T_(j,k), which is the "
                    + "corresponding entry of the transpose of M_n times M_n. The Riordan "
                    + "series contributing to column k contains X^k with constant "
                    + "coefficient one after that factor. Hence M_n is lower triangular "
                    + "with diagonal one. Its determinant is one, and multiplicativity "
                    + "together with invariance under transpose gives determinant one for "
                    + "the kernel matrix.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barry-2013-riordan-pascal-kernel-determinant"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula X() => F.Id("X");

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));

    private static Formula Fin(Formula n) => Call("Fin", Add(n, D(1)));

    private static Formula Inverse(Formula a)
    {
        var denominator = Subtract(D(1), Multiply(Call("C", a), X()));
        return Call("invOfUnit", denominator, D(1));
    }

    private static Formula RiordanEntry(
        Formula m,
        Formula a,
        Formula b,
        Formula n,
        Formula k)
    {
        var inverse = Inverse(a);
        var factor = Multiply(
            Multiply(X(), Add(D(1), Multiply(Call("C", b), X()))),
            Power(inverse, m));
        return Call("coeff", n,
            Multiply(inverse, Power(Parenthesized(factor), k)));
    }

    private static Formula BoundedSum(
        Formula index,
        Formula lower,
        Formula upper,
        Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Equal(index, lower)),
            Caret, Grp(upper), Sp, Parenthesized(summand));

    private static Formula RiordanFormula()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var b = F.Id("b");
        var n = F.Id("n");
        var k = F.Id("k");
        return Disp(Seq(
            Bound("m", Naturals()), Bound("a", Integers()), Bound("b", Integers()),
            Bound("n", Naturals()), Bound("k", Naturals()),
            Equal(Call("riordan", m, a, b, n, k), RiordanEntry(m, a, b, n, k))));
    }

    private static Formula PFormula()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var b = F.Id("b");
        var n = F.Id("n");
        var k = F.Id("k");
        var summand = Multiply(
            Call("C", Call("riordan", m, a, b, n, k)),
            Power(X(), k));
        return Disp(Seq(
            Bound("m", Naturals()), Bound("a", Integers()), Bound("b", Integers()),
            Bound("n", Naturals()),
            Equal(Call("P", m, a, b, n), BoundedSum(k, D(0), n, summand))));
    }

    private static Formula MFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var k = F.Id("k");
        var index = Fin(n);
        return Disp(Seq(
            Bound("n", Naturals()), Bound("i", index), Bound("k", index),
            Equal(Call("M", n, i, k),
                Call("riordan", D(2), D(1), D(1), Call("val", i), Call("val", k)))));
    }

    private static Formula DtildeFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var k = F.Id("k");
        var j = F.Id("j");
        var index = Fin(n);
        var polynomial = Call("P", D(2), D(1), D(1), j);
        var summand = Multiply(Call("map", F.Id("C"), polynomial), Call("C", polynomial));
        var kernel = BoundedSum(j, D(0), n, summand);
        return Disp(Seq(
            Bound("n", Naturals()), Bound("i", index), Bound("k", index),
            Equal(Call("Dtilde", n, i, k),
                Call("coeff", Call("val", k),
                    Call("coeff", Call("val", i), kernel)))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var matrix = Call("M", n);
        var dtilde = Call("Dtilde", n);
        var gram = Multiply(Call("transpose", matrix), matrix);
        var body = And(
            Equal(dtilde, gram),
            Equal(Call("det", dtilde), D(1)));
        return Disp(Seq(
            F.Id("claim"), Sp, Iff, Sp,
            Bound("n", Naturals()), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));
}
