using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SumProductSevenPointCellDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/SumProductSevenPointCell.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A seven-element set of positive reals with thirteen products has at least "
            + "twenty-four sums.",
        H("The Seven-Point Sum-Product Cell (23, 13) Is Absent"),
        Blocks(
            Node("geometric-sum-lower-bound", "Sums of seven geometric terms",
                "geometric_sum_card_lower_bound", GeometricFormula(),
                "For b positive and r greater than one, the seven terms b, br, through "
                    + "br to the sixth power have at least twenty-four distinct sums. "
                    + "Every equality of two unordered pair sums reduces to one of "
                    + "thirteen polynomial equations. Their twelve remaining factors "
                    + "have no common positive root, so removing at most four outer "
                    + "index pairs leaves an injective sum map.", DescribeRole.Theorem),
            Node("minimum-products-force-many-sums", "Thirteen products force twenty-four sums",
                "stronger_result", StrongerFormula(),
                "The minimum product cardinality of a seven-element positive-real set "
                    + "is thirteen. Equality forces a geometric progression. Applying "
                    + "the geometric sum bound gives at least twenty-four sums.",
                DescribeRole.Theorem),
            Node("seven-point-cell-claim", "The cell (23, 13) is absent", "claim",
                ClaimFormula(),
                "For every finite set A of positive reals with seven elements, the "
                    + "sumset cannot have twenty-three elements while the product set "
                    + "has thirteen elements. Both sets use pointwise operations.",
                DescribeRole.Definition),
            Node("seven-point-cell-excluded", "Exclusion of the cell (23, 13)", "result",
                Disp(F.Id("claim")),
                "The stronger bound contradicts the proposed sum cardinality "
                    + "whenever the product cardinality is thirteen.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("obryant-2024-sum-product-seven-point-cell"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Real() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Real"));

    private static Formula Positive(Formula a)
    {
        var x = F.Id("x");
        return All("x", Real(), Imp(
            new Formula.Relation(x, FormulaRelationOperator.MemberOf, a), Lt(D(0), x)));
    }

    private static Formula SumCard(Formula a) => Call("card", Add(a, a));
    private static Formula ProductCard(Formula a) => Call("card", Mul(a, a));

    private static Formula GeometricFormula()
    {
        var b = F.Id("b"); var r = F.Id("r"); var i = F.Id("i");
        var terms = new Formula.SetBuilder(Mul(b, new Formula.Power(r, i)), i,
            Call("range", D(7)));
        return Disp(All("b", Real(), All("r", Real(),
            Imp(Lt(D(0), b), Imp(Lt(D(1), r), Le(D(2, 4), SumCard(terms)))))));
    }

    private static Formula StrongerFormula()
    {
        var a = F.Id("A");
        return Disp(All("A", Call("Finset", Real()), Imp(Positive(a),
            Imp(Eq(Call("card", a), D(7)), Imp(Eq(ProductCard(a), D(1, 3)),
                Le(D(2, 4), SumCard(a)))))));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("A");
        var cell = And(Eq(SumCard(a), D(2, 3)), Eq(ProductCard(a), D(1, 3)));
        return Disp(Iff(F.Id("claim"), All("A", Call("Finset", Real()),
            Imp(Positive(a), Imp(Eq(Call("card", a), D(7)), new Formula.Not(cell))))));
    }
}
