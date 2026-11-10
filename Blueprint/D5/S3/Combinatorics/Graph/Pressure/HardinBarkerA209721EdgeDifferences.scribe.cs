using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Pressure;

internal sealed class HardinBarkerA209721EdgeDifferencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hardinbarker2012a209721");
    private const string NameQuote = "1/4 the number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences.";
    private const string FormulaQuote = "Empirical: a(n) = a(n-1) +2*a(n-2) -2*a(n-3). Empirical g.f.: x*(3+x-5*x^2)/((1-x)*(1-2*x^2)). [_Colin Barker_, Mar 23 2012]";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact three-column array counts, recurrence and formal generating series.",
        H("Hardin and Barker's three-column array formulas"),
        Blocks(
            Node("source-arrays", "The literal arrays", "IsSourceArray", ArrayFormula(),
                "OEIS A209721, revision 43, NAME: \"" + NameQuote + "\" Matrix has n+1 labelled rows and three labelled columns, with entries Fin 3. Fin.castSucc and Fin.succ select the two consecutive row or column positions. For each square with top row a,b and bottom row c,d the integer list is [b-a,d-b,c-d,a-c], and List.Pairwise tests that all differences are unequal. val is the natural representative, coerced to the integers before subtraction. Every adjacent square is tested; rotations, reflections and translations are not identified.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("source-count", "One quarter of the raw count", "a", CountFormula(),
                "OEIS A209721, revision 43, NAME: \"" + NameQuote + "\" Nat.card counts the full subtype of these labelled arrays. The result is coerced to the rationals and divided by rational four. Offset 1,1 restricts the source formulas to positive n; a is defined for every natural input.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("source-series", "Coefficients of the ordinary formal series", "IsSourceSeries", SeriesFormula(),
                "OEIS A209721, revision 43, FORMULA: \"Empirical g.f.: x*(3+x-5*x^2)/((1-x)*(1-2*x^2)). [_Colin Barker_, Mar 23 2012]\" With offset 1,1, the ordinary series has zero constant coefficient and coefficient a(n) for every n at least one. The carrier is PowerSeries over the rationals.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("source-claim", "Recurrence, existence and generating identity", "claim", Equal(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A209721, revision 43, FORMULA (the entry has no page numbers): " + FormulaQuote + " The recurrence index is m+4 for natural m, exactly the indices at least four. The series assertion includes existence and holds for every series with the specified coefficients. Multiplication by the denominator expresses the rational generating identity in PowerSeries, since its constant coefficient is one.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("settling-result", "The full three-column counting theorem", "result", ClaimBody(),
                "Reading consecutive rows gives an equivalence between the array subtype and walks in the exact 27-state compatibility graph. Prepending a state and taking the tail identify the finite successor fibers. Induction on arbitrary walk length proves the transfer count, including isolated states and disconnected graphs. The transfer vector satisfies u(n+4)+2*u(n+1)=u(n+3)+2*u(n+2); summing over starts and dividing by four gives the recurrence for the array count. PowerSeries.mk supplies a series with zero constant coefficient. Coefficient extensionality, the recurrence and a(1)=3, a(2)=4, a(3)=5 give the formal identity. No analytic convergence premise is used.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin-barker-a209721"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role, OpenProblemResolutionClaim? openProblemResolutionClaim = null) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: openProblemResolutionClaim);

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name)) :
            new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RatType() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula IntType() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula FinType(Formula n) => Call("Fin", n);
    private static Formula SeriesType() => Call("PowerSeries", RatType());
    private static Formula ArrayType(Formula n) => Call("Matrix", FinType(Add(n, D(1))), FinType(D(3)), FinType(D(3)));
    private static Formula Coeff(Formula n, Formula a) => Apply(Qualified("PowerSeries", "coeff"), n, a);

    private static Formula ClockwiseBody(Formula a, Formula b, Formula c, Formula d)
    {
        Formula z = IntType();
        Formula differences = Seq(OpenBracket,
            Subtract(Cast(Call("val", b), z), Cast(Call("val", a), z)), Comma, Sp,
            Subtract(Cast(Call("val", d), z), Cast(Call("val", b), z)), Comma, Sp,
            Subtract(Cast(Call("val", c), z), Cast(Call("val", d), z)), Comma, Sp,
            Subtract(Cast(Call("val", a), z), Cast(Call("val", c), z)), CloseBracket);
        Formula ne = Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp,
            F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, z, Sp, Mapsto, Sp, NotEqual(F.Id("x"), F.Id("y"))));
        return Apply(Qualified("List", "Pairwise"), ne, differences);
    }

    private static Formula ArrayFormula()
    {
        Formula n = F.Id("n"), x = F.Id("X"), i = F.Id("i"), j = F.Id("j");
        Formula ic = Apply(Qualified("Fin", "castSucc"), i), jc = Apply(Qualified("Fin", "castSucc"), j);
        Formula ii = Apply(Qualified("Fin", "succ"), i), jj = Apply(Qualified("Fin", "succ"), j);
        Formula body = All("i", FinType(n), All("j", FinType(D(2)), ClockwiseBody(
            Apply(x, ic, jc), Apply(x, ic, jj), Apply(x, ii, jc), Apply(x, ii, jj))));
        return All("n", NatType(), All("X", ArrayType(n), Equal(Call("IsSourceArray", x), Parenthesized(body))));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), x = F.Id("X");
        Formula subtype = Seq(OpenBrace, x, Sp, Colon, Sp, ArrayType(n), Sp, Slash, Slash, Sp,
            Call("IsSourceArray", x), CloseBrace);
        return All("n", NatType(), Equal(Call("a", n), new Formula.Fraction(
            Cast(Apply(Qualified("Nat", "card"), subtype), RatType()), D(4))));
    }

    private static Formula SeriesFormula()
    {
        Formula a = F.Id("A"), n = F.Id("n");
        Formula body = And(Equal(Coeff(D(0), a), D(0)), All("n", NatType(),
            Implies(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n), Equal(Coeff(n, a), Call("a", n)))));
        return All("A", SeriesType(), Equal(Call("IsSourceSeries", a), Parenthesized(body)));
    }

    private static Formula ClaimBody()
    {
        Formula m = F.Id("m"), a = F.Id("A"), x = Qualified("PowerSeries", "X");
        Formula recurrence = All("m", NatType(), Equal(Call("a", Add(m, D(4))),
            Subtract(Add(Call("a", Add(m, D(3))), Multiply(D(2), Call("a", Add(m, D(2))))),
                Multiply(D(2), Call("a", Add(m, D(1)))))));
        Formula existence = ExistsOne("A", SeriesType(), Call("IsSourceSeries", a));
        Formula denominator = Multiply(Parenthesized(Subtract(D(1), x)), Parenthesized(Subtract(D(1), Multiply(D(2), Pow(x, D(2))))));
        Formula numerator = Multiply(x, Parenthesized(Subtract(Add(D(3), x), Multiply(D(5), Pow(x, D(2))))));
        Formula identity = All("A", SeriesType(), Implies(Call("IsSourceSeries", a), Equal(Multiply(a, Parenthesized(denominator)), numerator)));
        return And(Parenthesized(recurrence), And(Parenthesized(existence), Parenthesized(identity)));
    }
}
