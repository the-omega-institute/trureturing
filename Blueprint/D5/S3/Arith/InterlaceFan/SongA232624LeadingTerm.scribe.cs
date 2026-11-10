using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.InterlaceFan;

internal sealed class SongA232624LeadingTermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PrimeForms/song2019a232624");
    private const string CoefficientQuotation =
        "a(n,m) = [x^m] MPR2(n, x), n >= 1, m=0, 1, ..., deg(n), with MPR2(n, x) the (monic) minimal polynomials of 2*cos(2*Pi/n), explained in a comment above. The degree is deg(1) = deg(2) = 1, deg(n) = phi(n)/2 = A023022(n), n >= 3 (phi is the Euler totient function A000010).";
    private const string ConjectureQuotation =
        "Conjecture: For odd n > 1, the term of the highest degree of (MPR2(2n, x) - MPR2(n, x))/2 is (-1)^omega(n) * x^(phi(n)/2-n/rad(n)) = A076479(n) * x^(A023022(n)-A003557(n)). For example, for n = 15, (MPR2(30, x) - MPR2(15, x))/2 = x^3 - 4x; for n = 105, (MPR2(210, x) - MPR2(105, x))/2 = -x^23 + ...; for n = 225, (MPR2(450, x) - MPR2(225, x))/2 = x^45 + ... If this is true, then for odd n > 1, a(n,A023022(n)-k) = a(2n,A023022(n)-k) = 0 for k = 1, 3, ..., A003557(n)-2; a(n,A023022(n)-A003557(n)) = -A076479(n) and a(2n,A023022(n)-A003557(n)) = A076479(n). - _Jianing Song_, Jul 11 2019";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact leading term of the difference of odd and doubled cosine minimal polynomials.",
        H("Song's conjecture in OEIS A232624"), Blocks(
            Paragraph(Text("The polynomials have coefficients in Q. MPR2 n is the minimal polynomial over Q of the stated real cosine. Nat.div denotes natural-number division; subtraction between natural numbers is truncated subtraction. For odd n > 1, m is positive and odd and m <= d, so d - m is the ordinary nonnegative difference. The variable e below denotes the rational sign written epsilon in the text. Multiplication by the rational one half is scalar multiplication of polynomials.")),
            Node("MPR2", "The real cosine minimal polynomial", MPR2Formula(),
                "OEIS A232624 revision 109, unpaginated Formula line: \"" + CoefficientQuotation + "\" The real number is 2 times Real.cos (2 times Real.pi divided by the real cast of n). The coefficient field of minpoly is Q.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The coefficient array", CoefficientFormula(),
                "OEIS A232624 revision 109, unpaginated Formula line: \"" + CoefficientQuotation + "\" Polynomial.coeff extends the array by zero above the degree; the source uses rows beginning at n = 1 and coefficient indices beginning at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The leading term and all coefficient consequences",
                Equal(Named("claim"), Parenthesized(ClaimBody())),
                "OEIS A232624 revision 109, unpaginated Comment line: \"" + ConjectureQuotation + "\" Nat.totient, UniqueFactorizationMonoid.radical and ArithmeticFunction.cardDistinctFactors express phi, rad and omega. Odd k and k < m express precisely 1, 3, ..., m - 2. The formula includes nonzeroness and every coefficient consequence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Song's leading term formula", ClaimBody(),
                "Möbius inversion in the power-series quotient by X raised to m + 1 leaves the unique factor indexed by rad(n) and n/rad(n). Its first nonconstant coefficient is minus e. Reflection at odd conductors makes the cyclotomic half-difference start with e times X raised to m. Homogeneous evaluation at X squared plus one and X identifies it with the reciprocal substitution of the actual cosine minimal-polynomial difference. Its lowest coefficient determines the degree and leading coefficient of that difference without cancellation. Reflection then gives every displayed coefficient identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("song232624-leadingterm"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolutionClaim = null) =>
        Describe.Lean(DescribeId.Create("song232624-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolutionClaim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Call(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rats() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula All(string name, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), Nats())], body);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesTo(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Named("let"), Sp, Equal(Seq(F.Id(name), Colon, Sp, type), value), Semi, Sp, body);
    private static Formula Subtract(Formula left, Formula right) => Seq(left, Minus, right);
    private static Formula Twice(Formula value) => Seq(D(2), Cdot, Sp, value);
    private static Formula Coeff(Formula p, Formula j) => Call(Seq(Parenthesized(p), Dot, Named("coeff")), j);

    private static Formula MPR2Formula()
    {
        Formula n = F.Id("n");
        Formula angle = new Formula.Fraction(Twice(Qualified("Real", "pi")), Cast(n, Reals()));
        Formula value = Seq(Cast(D(2), Reals()), Cdot, Sp, Call(Qualified("Real", "cos"), angle));
        return All("n", Equal(Call("MPR2", n), Call("minpoly", Rats(), value)));
    }

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        return All("n", All("j", Equal(Call("a", n, j), Coeff(Call("MPR2", n), j))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula m = F.Id("m");
        Formula e = F.Id("e");
        Formula f = F.Id("F");
        Formula k = F.Id("k");
        Formula vanish = All("k", ImpliesTo(Call("Odd", k), ImpliesTo(Less(k, m),
            And(Equal(Call("a", n, Subtract(d, k)), D(0)),
                Equal(Call("a", Twice(n), Subtract(d, k)), D(0))))));
        Formula conclusions = And(NotEqual(f, D(0)),
            And(Equal(Seq(f, Dot, Named("natDegree")), Subtract(d, m)),
            And(Equal(Seq(f, Dot, Named("leadingCoeff")), e),
            And(vanish, And(Equal(Call("a", n, Subtract(d, m)), Seq(Minus, e)),
                Equal(Call("a", Twice(n), Subtract(d, m)), e))))));
        Formula difference = Seq(Cast(new Formula.Fraction(D(1), D(2)), Rats()), Cdot, Sp,
            Parenthesized(Subtract(Call("MPR2", Twice(n)), Call("MPR2", n))));
        Formula sign = new Formula.Power(Cast(Seq(Minus, D(1)), Rats()),
            Call(Qualified("ArithmeticFunction", "cardDistinctFactors"), n));
        Formula radical = Call(Qualified("UniqueFactorizationMonoid", "radical"), n);
        Formula body = Let("d", Nats(), Call(Qualified("Nat", "div"), Call(Qualified("Nat", "totient"), n), D(2)),
            Let("m", Nats(), Call(Qualified("Nat", "div"), n, radical),
            Let("e", Rats(), sign,
            Let("F", Call("Polynomial", Rats()), difference, conclusions))));
        return All("n", ImpliesTo(Call("Odd", n), ImpliesTo(Less(D(1), n), body)));
    }
}
