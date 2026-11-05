using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RowmotionExceptionalGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.";
    private static readonly Formula N = F.Id("n");
    private static readonly Formula I = F.Id("I");
    private static readonly Formula State = Call("Set", Call("Product", Call("Fin", D(3)), Call("Fin", N)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting convex rectangle states outside the separated endpoint family.",
        H("Geometric exceptional states in three rows"),
        Blocks(
            Paragraph(Text("The state space consists of actual subsets of Fin 3 times Fin n, ordered coordinatewise. An interval-closed subset contains every point between each pair of its comparable members. Native column x corresponds to source column x+1. All counts include the empty subset.")),
            Node("convexStates", "The complete convex state space", DescribeRole.Definition,
                All("n", F.Id("Nat"), All("I", State,
                    Iff(Member(I, Call("convexStates", N)), Call("OrdConnected", I)))),
                "convexStates(n) is the finite set of every interval-closed subset of the rectangle, with no row-nonemptiness condition."),
            Node("exceptionalGeometry", "The complement of separated endpoint states", DescribeRole.Definition,
                All("n", F.Id("Nat"), All("I", State,
                    Iff(Member(I, Call("exceptionalGeometry", N)),
                        And(Call("OrdConnected", I), new Formula.Not(Call("Separated", I)))))),
                "Separated is the existing actual-set predicate: the three rows are intervals [a(r),b(r)], both endpoint sequences are strictly decreasing, and every pair among the six indexed sites a(0),a(1),a(2),b(0)+2,b(1)+2,b(2)+2 has circular distance at least eight on the circle of length n+4. Repeated occurrences fail this condition."),
            Node("missingRowStates", "Convex states with an empty row", DescribeRole.Definition,
                All("n", F.Id("Nat"), All("I", State,
                    Iff(Member(I, Call("missingRowStates", N)),
                        And(Call("OrdConnected", I), Call("HasEmptyRow", I))))),
                "HasEmptyRow(I) means that there exists r in Fin 3 such that (r,x) is absent from I for every x in Fin n. It permits other rows to be empty as well."),
            Node("missing_row_bound", "Four endpoints suffice after an empty row", DescribeRole.Theorem,
                All("n", F.Id("Nat"), Imp(Le(D(2), N),
                    Le(Card(Call("missingRowStates", N)), Mul(D(3), Pow(N, D(4)))))),
                "For every n at least two, choose one empty row. Convexity makes each remaining row an interval. A nonempty row is encoded by its least and greatest columns; an empty row is encoded by endpoints 1 and 0. Thus every state is in the image of Fin 3 times the space of two pairs of Fin n endpoints. Multiple encodings only reduce the image cardinality."),
            Node("exceptional_geometry_bound", "The full-carrier separated complement bound", DescribeRole.Theorem,
                All("n", F.Id("Nat"), Imp(Le(D(1, 1), N),
                    Le(Card(Call("exceptionalGeometry", N)), Mul(D(2, 3, 3), Pow(N, D(5)))))),
                "For every n at least eleven, the number of convex states outside the separated family is at most 233 n^5. Missing-row states contribute at most 3 n^4. For a state meeting every row, convexity forces both endpoint sequences to be weakly decreasing. If all indexed shifted sites pass the distance test, equal endpoints are excluded and both sequences become strictly decreasing, giving separated endpoint data for the same actual set. Otherwise one of the fifteen indexed pairs has circular distance below eight. Fix the other five raw endpoints. The remaining shifted site has at most fifteen positions: its signed circular offset lies in the integer interval [-7,7], and raw columns inject into offsets because their interval is shorter than n+4. A fiber count and the union bound give at most 225 n^5 full-row failures. Consequently the total is at most 225 n^5+3 n^4, which is at most 233 n^5."),
            Paragraph(Text("This is a geometric complement estimate. A bound for failures of a literal rowmotion return additionally requires the global decoder transition and return reflection. The least-positive-period bound also requires a count of the union of every shorter-return class. No assertion about these dynamics or about all separated states having the same least period follows from the complement count alone.")))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("rowmotion-geometry-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] arguments) => Seq(F.Id(name), Open,
        Seq(arguments.SelectMany((value, index) => index == 0 ? new[] { value } : new[] { Comma, Sp, value }).ToArray()), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Member(Formula a, Formula b) => Call("Member", a, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Card(Formula a) => Call("card", a);
}
