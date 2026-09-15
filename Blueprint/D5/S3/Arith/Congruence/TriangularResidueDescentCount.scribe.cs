using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class TriangularResidueDescentCountDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/TriangularResidueDescentCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/kagey2019a329278");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kagey's descent count for the triangular-number permutation modulo a positive power of two.",
        H("The Triangular-Residue Descent Count"),
        Blocks(
            Node("T", "Triangular residues", TFormula(),
                "For positive n and natural k, T(n,k) is the k-th triangular number reduced "
                    + "modulo 2^n, giving row n of A329278 with offset zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("descents", "Adjacent strict descents", DescentsFormula(),
                "For positive n, descents(n) counts the indices k from zero through 2^n-2 "
                    + "at which T(n,k) is strictly greater than T(n,k+1).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("kagey_a329278", "Kagey's descent formula", TheoremFormula(),
                "For positive n, put M=2^n and A(j)=j(j+1)/2. Induction on j at most M-1 "
                    + "shows that the number of descents before j is A(j) divided by M: "
                    + "both quantities increase by one exactly when the next residue wraps. "
                    + "At j=M-1, the terminal quotient is 2^(n-1)-1.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a329278-triangular-residue-descent-count"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a329278-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula TFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var triangular = new Formula.Fraction(
            Multiply(k, Parenthesized(Add(k, D(1)))), D(2));
        return Disp(Universal(["n", "k"], Equal(
            Call("T", n, k), Call("mod", triangular, Power(D(2), n)))));
    }

    private static Formula DescentsFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var descent = Less(Call("T", n, Add(k, D(1))), Call("T", n, k));
        var indices = Call("range", Subtract(Power(D(2), n), D(1)));
        return Disp(Universal(["n"], Equal(
            Call("descents", n), Call("card", Call("filter", Lambda(k, descent), indices)))));
    }

    private static Formula TheoremFormula()
    {
        var n = F.Id("n");
        return Disp(Universal(["n"], Implies(
            Less(D(0), n),
            Equal(Call("descents", n), Subtract(Power(D(2), Subtract(n, D(1))), D(1))))));
    }

    private static Formula Naturals() => F.Id("N");

    private static Formula Universal(string[] variables, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. variables.Select(variable =>
                new Formula.BoundVariable(FormulaIdentifier.Create(variable), Naturals()))],
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(variable, Sp, Mapsto, Sp, body));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
