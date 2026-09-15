using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class StephanLeastCoordinateDistinctnessRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PrimeForms/stephan2013a229140");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The values 628 and 673 refute the distinctness conjecture for OEIS A229140.",
        H("The OEIS A229140 Least-Coordinate Distinctness Conjecture"),
        Blocks(
            Node("least-first-coordinate", "The least first coordinate",
                IsLeastCoordFormula(),
                "For natural m and x, IsLeastCoord(m,x) holds exactly when x occurs as "
                    + "the first coordinate of a representation of m by two natural squares "
                    + "and no smaller natural first coordinate occurs in such a representation.",
                "IsLeastCoord", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("least-coordinate-distinctness", "Distinctness between consecutive zeros",
                ClaimFormula(),
                "For every pair L<R whose least first coordinates are zero, with no value "
                    + "strictly between them having least first coordinate zero, any two "
                    + "distinct intermediate representable values cannot have the same least "
                    + "first coordinate.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("least-coordinate-distinctness-refuted", "The conjecture fails between 625 and 676",
                ResultFormula(),
                "The proof checks the zero witnesses 625=0^2+25^2 and 676=0^2+26^2, "
                    + "the representations 628=12^2+22^2 and 673=12^2+23^2, the exclusion "
                    + "of every first coordinate from 0 through 11 for each intermediate value, "
                    + "and the absence of a natural square strictly between 625 and 676. Thus "
                    + "628 and 673 share the least first coordinate 12.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a229140-stephan-least-coordinate-distinctness-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula IsLeastCoordFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var y = F.Id("y");
        var u = F.Id("u");
        var v = F.Id("v");
        var representation = ExistsOverNaturals("y", Equal(
            Add(Power(x), Power(y)), m));
        var excludesSmaller = Universal("u", Implies(
            Less(u, x),
            Universal("v", NotEqual(Add(Power(u), Power(v)), m))));
        return Disp(Universal("m", Universal("x", Iff(
            Call("IsLeastCoord", m, x),
            And(representation, excludesSmaller)))));
    }

    private static Formula ClaimFormula()
    {
        var left = F.Id("L");
        var right = F.Id("R");
        var m = F.Id("m");
        var n = F.Id("n");
        var k = F.Id("k");
        var noIntermediateZero = Universal("m", Implies(
            Less(left, m),
            Less(m, right),
            new Formula.Not(Call("IsLeastCoord", m, D(0)))));
        var distinctness = Universal("m", Universal("n", Universal("k", Implies(
            Less(left, m),
            Less(m, right),
            Less(left, n),
            Less(n, right),
            NotEqual(m, n),
            Call("IsLeastCoord", m, k),
            Call("IsLeastCoord", n, k),
            F.Id("False")))));
        var quantified = Universal("L", Universal("R", Implies(
            Call("IsLeastCoord", left, D(0)),
            Call("IsLeastCoord", right, D(0)),
            Less(left, right),
            noIntermediateZero,
            distinctness)));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula ExistsOverNaturals(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Implies(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.Implies, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Power(Formula value) =>
        new Formula.Power(value, D(2));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
