using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class ConeLineEndpointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated actual boundary endpoints in every interior cone direction.",
        H("Off-axis lines through a salient cone"),
        Blocks(
            Paragraph(Text("Let C be a closed salient convex cone in a real normed vector space, e an interior point, and x a vector outside the real span of e. There are real numbers a<b such that te-x belongs to the negative cone exactly when t is at most a, and belongs to C exactly when t is at least b. The points -(ae-x) and be-x belong to the entire topological boundary of C. No normalization functional, finite-dimensional coordinate system or polynomial is assumed.")),
            Describe.Lean(
                DescribeId.Create("off-axis-closed-rays"),
                DeclarationHandle.Create("D5/S3/Geometry/AlgebraicBoundary/ConeLineEndpoints.off_axis_closed_rays"),
                H("Two strictly separated finite boundary endpoints"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Since e is interior, e-x/t belongs to C for sufficiently large positive t. Positive scaling gives te-x in C. Cone addition makes the set of such parameters an upper set. Applying the same observation to -x supplies a point in the negative cone. Salience and the off-axis condition prevent any point of the line from belonging to both cones, which bounds the upper set below. Closedness then identifies it with a closed ray starting at its infimum. The continuous preimage boundary inclusion places the endpoint on the actual cone boundary. Repeating the construction with -x gives the negative closed ray, and salience gives the strict gap.")),
                    Paragraph(Text("This proves the geometric endpoint assertion for every interior direction and every off-axis translate. To obtain real-rootedness of a boundary polynomial, one must still prove that its restrictions have the claimed degree, vanish at these two endpoints, and account for every root with multiplicity. Axis translates require a separate homogeneous polynomial identity."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var real = F.Id("Real");
        var e = F.Id("E");
        var cone = F.Id("C");
        var direction = F.Id("e");
        var x = F.Id("x");
        Formula Y(Formula t) => Call("sub", Call("smul", t, direction), x);
        var a = F.Id("a");
        var b = F.Id("b");
        var t = F.Id("t");
        var rays = And(Rel(a, FormulaRelationOperator.LessThan, b),
            All("t", real, Iff(Member(Call("neg", Y(t)), cone),
                Rel(t, FormulaRelationOperator.LessThanOrEqual, a))),
            All("t", real, Iff(Member(Y(t), cone),
                Rel(b, FormulaRelationOperator.LessThanOrEqual, t))),
            Member(Call("neg", Y(a)), Call("frontier", cone)),
            Member(Y(b), Call("frontier", cone)));
        var offAxis = All("s", real, Call("NotEqual", x, Call("smul", F.Id("s"), direction)));
        return All("E", F.Id("RealNormedVectorSpace"),
            All("C", Call("ConvexCone", real, e), All("e", e, All("x", e,
                Imp(And(Call("IsClosed", cone), Call("Salient", cone),
                    Member(direction, Call("interior", cone)), offAxis),
                    Exists("a", real, Exists("b", real, rays)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Member(Formula a, Formula b) =>
        Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] parts)
    {
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
}
