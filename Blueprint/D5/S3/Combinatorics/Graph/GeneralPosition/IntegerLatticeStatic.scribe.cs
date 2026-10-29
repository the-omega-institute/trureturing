using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.GeneralPosition;

internal sealed class IntegerLatticeStaticDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/klavzaretal2026mobileproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate general position in dimension n+1 has sharp cardinality 2 raised to 2 raised to n.",
        H("Sharp coordinate general position in integer lattices"),
        Blocks(
            Paragraph(Text("Vertices are integer-valued functions on Fin k. Coordinate betweenness uses weak inequalities, so equal coordinates are included. The declarations are in the Lean namespace IntegerLatticeStatic. These statements concern finite static sets. Section 5 of Moving through Cartesian products, coronas and joins in general position cites Theorem 1 of Klavzar and Rus, The general position number of integer lattices, DOI 10.1016/j.amc.2020.125664, for the underlying static extremum.")),
            Node("between", "Weak coordinate betweenness", "Between", DescribeRole.Definition,
                BetweenFormula(),
                AssessedProvenance.FromRepo(Source),
                "The middle point may be increasing in one coordinate and decreasing in another. Endpoints may agree in any coordinate."),
            Node("coordinate-gp", "Coordinate general position", "CoordinateGP", DescribeRole.Definition,
                GeneralPositionFormula(),
                AssessedProvenance.FromRepo(Source),
                "Every ordered triple of pairwise distinct members is excluded from coordinate betweenness. The condition does not assume that coordinate projections are injective."),
            Node("upper-bound", "The static upper bound", "card_le", DescribeRole.Theorem,
                UpperFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Section 5, second bullet, cites the static value in dimension k. Here k=n+1. Each of the 2 raised to n sign patterns orients the last n coordinates, while the first coordinate increases. A point is labelled by the orientations in which it has a distinct predecessor. Equal labels on two distinct points would give a three-point chain in one orientation, contradicting general position. Thus the labels inject the set into the subsets of the sign-pattern set."),
            Node("attainment", "A bounded attaining set with injective coordinates", "exists_attaining",
                DescribeRole.Theorem, AttainmentFormula(),
                AssessedProvenance.FromRepo(Source),
                "Start with the two points zero and one in dimension one. From an array A with N points, use pairs (p,r) as indices. The old coordinates become N times A(p,j) plus A(r,j); the additional first coordinate is N times A(p,0) plus N minus one minus A(r,0). All coordinates lie between zero and N squared minus one and remain injective. Three distinct blocks reduce to the preceding general-position property. One block reduces to the second indices. For exactly two equal blocks, the ordinary and reversed first coordinates force the two second indices to agree. Cardinality squares at every step, giving the stated power. No motion sequence is asserted.")),
        []));

    private static Formula BetweenFormula()
    {
        var increasing = And(Leq(Coord("x"), Coord("y")), Leq(Coord("y"), Coord("z")));
        var decreasing = And(Leq(Coord("z"), Coord("y")), Leq(Coord("y"), Coord("x")));
        var body = IffFormula(Call("Between", X("x"), X("y"), X("z")),
            All("j", Fin(X("k")), Or(increasing, decreasing)));
        return All("k", Nat(), All("x", Vertex(X("k")),
            All("y", Vertex(X("k")), All("z", Vertex(X("k")), body))));
    }

    private static Formula GeneralPositionFormula()
    {
        var distinctTriple = Imp(Ne(X("x"), X("y")), Imp(Ne(X("y"), X("z")),
            Imp(Ne(X("x"), X("z")), Not(Call("Between", X("x"), X("y"), X("z"))))));
        var body = IffFormula(Call("CoordinateGP", X("S")),
            Members("x", Members("y", Members("z", distinctTriple))));
        return All("k", Nat(), All("S", Call("Finset", Vertex(X("k"))), body));
    }

    private static Formula UpperFormula()
    {
        var body = Imp(Call("CoordinateGP", X("S")), Leq(Call("card", X("S")), Bound()));
        return All("n", Nat(), All("S", Call("Finset", Vertex(Add(X("n"), D(1)))), body));
    }

    private static Formula AttainmentFormula()
    {
        var dimension = Add(X("n"), D(1));
        var bounds = Members("x", All("j", Fin(dimension),
            And(Leq(D(0), Coord("x")), Lt(Coord("x"), Bound()))));
        var injective = All("j", Fin(dimension), Members("x", Members("y",
            Imp(Eq(Coord("x"), Coord("y")), Eq(X("x"), X("y"))))));
        var body = And(Call("CoordinateGP", X("S")), And(Eq(Call("card", X("S")), Bound()),
            And(Call("Nonempty", X("S")), And(bounds, injective))));
        return All("n", Nat(), Ex("S", Call("Finset", Vertex(dimension)), body));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Vertex(Formula size) =>
        Seq(Fin(size), Sp, Rightarrow, Sp, new Formula.NamedConstant(FormulaIdentifier.Create("Int")));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, X(name), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, X(name), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Members(string name, Formula body) =>
        Seq(Forall, Sp, X(name), Sp, InMacro, Sp, X("S"), Comma, Sp, body);
    private static Formula Coord(string point) => Call(point, X("j"));
    private static Formula Bound() => new Formula.Power(D(2), new Formula.Power(D(2), X("n")));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, Open, a, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
}
