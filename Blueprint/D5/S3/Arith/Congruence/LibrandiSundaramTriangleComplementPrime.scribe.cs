using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class LibrandiSundaramTriangleComplementPrimeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/librandi2012a140869");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Librandi's triangle complement maps every outside value to a prime 4h+5.",
        H("Librandi's Sundaram-Type Triangle Complement"),
        Blocks(
            Node("T", "The triangle row formula", TFormula(),
                "For natural m and n, T is the displayed natural-number quotient. The subtraction "
                    + "and division are literal truncated natural operations; on m >= n >= 1 the "
                    + "numerator is at least two, so the formula has its intended value.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("InTriangle", "Membership in the triangle", InTriangleFormula(),
                "A natural h belongs to the triangle exactly when it is T(m,n) for natural "
                    + "coordinates with 1 <= n <= m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("librandi_a140869", "The complement-prime theorem", TheoremFormula(),
                "Assume that 4h+5 is composite. A nontrivial divisor supplied by the factorization "
                    + "theorem gives two odd factors. Writing them as 2a+1 and 2b+1, ordering the "
                    + "half-factors, and normalizing their product identity produces T(a,b)=h, a "
                    + "contradiction. The converse is false at h = 2, 8, and 12.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a140869-sundaram-triangle-complement-prime"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a140869-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula TFormula()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var product = Multiply(Multiply(D(2), m), n);
        var numerator = Subtract(Add(Add(product, m), n), D(2));
        return Disp(ForAll([Bound("m"), Bound("n")],
            Equal(Call("T", m, n), new Formula.Floor(new Formula.Fraction(numerator, D(2))))));
    }

    private static Formula InTriangleFormula()
    {
        var h = F.Id("h");
        var m = F.Id("m");
        var n = F.Id("n");
        var conditions = And(
            LessOrEqual(D(1), n),
            And(LessOrEqual(n, m), Equal(Call("T", m, n), h)));
        var witnesses = Parenthesized(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("m"), Bound("n")],
            conditions));
        return Disp(ForAll([Bound("h")],
            new Formula.Logic(Call("InTriangle", h), FormulaLogicOperator.Iff, witnesses)));
    }

    private static Formula TheoremFormula()
    {
        var h = F.Id("h");
        return Disp(ForAll([Bound("h")],
            Implies(new Formula.Not(Call("InTriangle", h)),
                Call("Prime", Add(Multiply(D(4), h), D(5))))));
    }

    private static Formula.BoundVariable Bound(string name) => new Formula.BoundVariable(
        FormulaIdentifier.Create(name), Naturals());

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [.. variables],
        body);

    private static Formula Naturals() => new Formula.LatexGroup([Mathbb, Sp, F.Id("N")]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
