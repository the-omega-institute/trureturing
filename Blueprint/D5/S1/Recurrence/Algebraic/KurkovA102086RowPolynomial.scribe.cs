using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KurkovA102086RowPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/kurkov2026a102086");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kurkov's complete A102086 row-polynomial identity, including existence of both source tables.",
        H("Kurkov's A102086 Row Polynomials"), Blocks(
            Paragraph(Text("The coefficient ring is Z and the variable X is formal. Rows and matrix columns are natural numbers starting at zero; P has an integer second index, including negative exterior indices. C embeds an integer as a constant polynomial. A row polynomial reads coefficients in displayed order, without reversal. All sums below are finite. Natural subtraction n-1 occurs only under k<n; the polynomial interior 0<b<a likewise forces a>0. At (0,0), the two boundary prescriptions agree because X^0=1.")),
            Node("IsSourceTriangle", "The source matrix", TriangleFormula(),
                "OEIS NAME: Triangular matrix, read by rows, that satisfies: T(n,k) = [T^2](n-1,k) when n>k>=0, with T(n,n) = (n+1). Lower triangularity reduces its ordinary matrix-square entry to j in [k,n). The displayed row zero is [1].", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourcePolynomialTable", "The polynomial table", TableFormula(),
                "Kurkov's FORMULA: Conjecture: n-th row polynomial is P(n+1, n) where P(n, k) = P(n, k-1) + (k+1) * P(n-1, k) for 0 < k < n with P(n, n) = x^n, P(n, 0) = 1, P(n, k) = 0 for k < 0 or k > n. The attribution is Mikhail Kurkov, Jul 03 2026. No numerical value is substituted for X.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete nonvacuous conjecture", Disp(Seq(Named("claim"), Sp, Iff, Sp, ClaimBody())),
                "Both source tables must exist. The identity is then required for every pair of source tables and every natural n, including n=0. There is no cutoff, extra hypothesis, coefficient reversal or alteration of any boundary.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The complete row-polynomial identity", Disp(ClaimBody()),
                "Construct P by recursion on a+b in the triangular domain, taking the base and diagonal values first, then extend to all integer exterior indices by zero. Both recursive interior arguments decrease a+b. Induction in a and then b proves uniqueness, and proves that P(a,b) has no coefficient above b. Put R_j=P(j+1,j). Define the Z-linear map L using Mathlib's Polynomial.lsum so that L(X^j)=R_j. This is independent of any matrix table. Induction in a and b gives L(P(a,b))=P(a+1,b) for 0<=b<=a: the base uses R_0=1, the diagonal uses the monomial rule, and the interior uses linearity and the source recurrence. At (n+2,n+1) the recurrence gives R_(n+1)=L(R_n)+(n+2)X^(n+1). Expanding R_n over its finite support gives L(R_n)=sum_(j=0)^n [X^j]R_n R_j. Taking coefficients yields the source matrix diagonal and its exact square recurrence; terms j<k vanish by the coefficient bound. Thus the coefficient table is an actual source T. Strong row induction proves uniqueness of T, since each factor on the right has row below n. Polynomial reconstruction gives the identity for the constructed pair. Uniqueness of P and T transports it to every source pair. The proof includes row zero and supplies both existential witnesses. This is a repository derivation using classical finite linear algebra; the bounded source screen supplies no worldwide priority or complete literature claim.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a102086-row-polynomial"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a102086-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Poly() => Seq(Z(), F.OpenBracket, F.Id("X"), F.CloseBracket);
    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula V(string s, params Formula[] xs) => new Formula.Apply(F.Id(s), [.. xs]);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Named(s), [.. xs]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string s, Formula ty, Formula body) => Seq(Forall, Sp, Par(Seq(F.Id(s), Colon, Sp, ty)), Comma, Sp, body);
    private static Formula Ex(string s, Formula ty, Formula body) => Seq(Exists, Sp, Par(Seq(F.Id(s), Colon, Sp, ty)), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula TType() => Arrow(N(), Arrow(N(), Z()));
    private static Formula PType() => Arrow(N(), Arrow(Z(), Poly()));
    private static Formula Sum(Formula index, Formula body) => Seq(new Formula.Subscript(F.Sum, index), Sp, Par(body));
    private static Formula TriangleFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), j = F.Id("j");
        Formula interval = new Formula.Apply(Seq(Named("Finset"), Dot, Named("Ico")), [k, n]);
        Formula rhs = Sum(Seq(j, Sp, InMacro, Sp, interval), Mul(V("T", Sub(n, D(1)), j), V("T", j, k)));
        Formula body = And(All("n", N(), All("k", N(), Imp(Lt(n, k), Eq(V("T", n, k), D(0))))),
            And(All("n", N(), Eq(V("T", n, n), Add(n, D(1)))),
                All("n", N(), All("k", N(), Imp(Lt(k, n), Eq(V("T", n, k), rhs))))));
        return Disp(All("T", TType(), Seq(Call("IsSourceTriangle", F.Id("T")), Sp, Iff, Sp, body)));
    }
    private static Formula TableFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula diagonal = All("a", N(), Eq(V("P", a, a), Pow(F.Id("X"), a)));
        Formula zero = All("a", N(), Eq(V("P", a, D(0)), D(1)));
        Formula exterior = All("a", N(), All("b", Z(),
            Imp(Or(Lt(b, D(0)), Lt(a, b)), Eq(V("P", a, b), D(0)))));
        Formula rhs = Add(V("P", a, Sub(b, D(1))),
            Mul(Call("C", Add(b, D(1))), V("P", Sub(a, D(1)), b)));
        Formula interior = All("a", N(), All("b", Z(),
            Imp(Lt(D(0), b), Imp(Lt(b, a), Eq(V("P", a, b), rhs)))));
        Formula body = And(diagonal, And(zero, And(exterior, interior)));
        return Disp(All("P", PType(), Seq(Call("IsSourcePolynomialTable", F.Id("P")), Sp, Iff, Sp, body)));
    }
    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula row = Sum(Seq(k, Sp, InMacro, Sp, new Formula.Apply(Seq(Named("Finset"), Dot, Named("range")), [Add(n, D(1))])),
            Mul(Call("C", V("T", n, k)), Pow(F.Id("X"), k)));
        return And(Ex("T", TType(), Call("IsSourceTriangle", F.Id("T"))),
            And(Ex("P", PType(), Call("IsSourcePolynomialTable", F.Id("P"))),
                All("T", TType(), All("P", PType(), Imp(Call("IsSourceTriangle", F.Id("T")),
                    Imp(Call("IsSourcePolynomialTable", F.Id("P")), All("n", N(), Eq(row, V("P", Add(n, D(1)), n)))))))));
    }
}
