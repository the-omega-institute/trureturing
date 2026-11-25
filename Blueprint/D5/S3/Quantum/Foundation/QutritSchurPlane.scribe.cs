using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class QutritSchurPlaneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original pure lifts fill the qutrit quotient four-plane.",
        H("An affine four-plane of original pure qutrit quotient images"), Blocks(
            Describe.Lean(DescribeId.Create("original-qutrit-quotient-affine-plane"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/QutritSchurPlane.original_qutrit_quotient_affine_plane"),
                H("The full support-one section"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026ssa")),
                Blocks(
                    Paragraph(Text("Let C be a pointed cone in a finite-dimensional real normed vector space V with real-linear unit u strictly positive off zero in C. An original pure state is an extreme point of the full u = 1 base. Every pair of distinct original pure states is assumed to generate an actual face with a whole affine ball chart. The actual cone faces F and J have real-linear coordinates on their whole spans carrying their cones to the full complex Hermitian three-by-three positive semidefinite cone and their normalization to the trace. Their actual intersection B has real span of dimension four. The real-linear g is nonnegative on C and its zero set in C is exactly F.")),
                    Paragraph(Text("The span of each face D is written S(D). The map pi is the quotient by S(F), and gQ is the real-linear functional on the quotient with gQ composed with pi equal to g. The set R comprises all positive multiples of original pure states in J outside F for which g is one. The theorem gives the equality of the homogeneous intersection with S(B) and identifies the image of R with the whole gQ = 1 slice of pi(S(J)). This slice is an affine translate of the range of an injective real-linear map from two complex coordinates and has four real direction dimensions.")),
                    Paragraph(Text("In J, the positive Hermitian representative of g can be diagonalized by a unitary change of coordinates. A positive eigenvalue gives a pivot. Positive matrices in B have zero pivot column by positivity of the quadratic form. Comparing dimensions shows that their real span fills the entire lower Hermitian block. The pivot reading therefore determines g on J, and the quotient kills the lower block. For each off-column, a rank-one outer product with the prescribed positive pivot gives the Schur completion. Trace normalization and faciality give an original pure state for this completion. Equality of two such quotient images implies equality of the original lifts by QutritPureLift, which recovers the off-column and determines the homogeneous intersection.")),
                    Paragraph(Text("This supplies the local binary-intersection step for the carrier dimension seventeen route to XIII160.34. Its scope is static state geometry and quotient reconstruction. Global incidence, topology, dynamical laws, physical clocks, energy, and thermodynamic cost require separate results."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula App(Formula a, Formula b) => new Formula.Apply(a, [b]);

    private static Formula Statement()
    {
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var v = F.Id("V");
        var cone = F.Id("C");
        var f = F.Id("F");
        var j = F.Id("J");
        var b = F.Id("B");
        var u = F.Id("u");
        var g = F.Id("g");
        var eF = F.Id("eF");
        var eJ = F.Id("eJ");
        var x = F.Id("x");
        var r = F.Id("r");
        var p = F.Id("p");
        var a = F.Id("a");
        var q = F.Id("q");
        var q0 = F.Id("q0");
        var gQ = F.Id("gQ");
        var l = F.Id("L");
        var pi = Call("mkQ", Call("span", real, f));
        var qtype = Call("quotient", v, Call("span", real, f));
        var hermitian = Call("HermitianMat", Call("Fin", D(3)), complex);
        Formula Span(Formula face) => Call("span", real, face);
        Formula Chart(Formula face) => Call("LinearEquiv", real, Span(face), hermitian);
        Formula Coordinates(Formula face, Formula e) => All("x", Span(face), And(
            new Formula.Logic(In(Call("val", x), face), FormulaLogicOperator.Iff, Le(D(0), App(e, x))),
            Eq(Call("trace", App(e, x)), App(u, Call("val", x)))));
        var strict = All("x", v, Imp(And(In(x, cone), new Formula.Not(Eq(x, D(0)))), Lt(D(0), App(u, x))));
        var support = All("x", v, Imp(In(x, cone), And(Le(D(0), App(g, x)),
            new Formula.Logic(Eq(App(g, x), D(0)), FormulaLogicOperator.Iff, In(x, f)))));
        var hypotheses = And(strict, And(support, And(Call("wholePairBalls", cone, u),
            And(Eq(b, Call("intersection", f, j)), And(Eq(Call("finrank", real, Span(b)), D(4)),
                And(Coordinates(f, eF), Coordinates(j, eJ)))))));
        var rays = Call("setOf", Seq(r, Mapsto, Sp, Ex("p", Call("pure", cone, u),
            Ex("a", real, And(In(Call("val", p), j), And(new Formula.Not(In(Call("val", p), f)),
                And(Lt(D(0), a), And(Eq(r, Call("smul", a, Call("val", p))), Eq(App(g, r), D(1))))))))));
        var slice = Call("setOf", Seq(q, Mapsto, Sp, And(In(q, Call("map", pi, Span(j))), Eq(App(gQ, q), D(1)))));
        var direction = Call("range", l);
        var witness = Ex("gQ", Call("LinearMap", real, qtype, real),
            Ex("q0", qtype, Ex("L", Call("LinearMap", real, Call("functions", Call("Fin", D(2)), complex), qtype),
                And(Eq(Call("comp", gQ, pi), g), And(Call("Injective", l),
                    And(Eq(Call("finrank", real, direction), D(4)),
                        And(Eq(Call("image", pi, rays), slice), Eq(slice, Call("affineSubspace", q0, direction)))))))));
        var result = And(Eq(Call("inf", Span(f), Span(j)), Span(b)), witness);
        var lin = Call("LinearMap", real, v, real);
        var faceType = Call("Face", cone);
        return All("V", F.Id("Type"), Seq(OpenBracket, Call("NormedAddCommGroup", v), CloseBracket, Sp,
            OpenBracket, Call("NormedSpace", real, v), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", real, v), CloseBracket, Sp,
            All("C", Call("PointedCone", real, v), All("u", lin, All("g", lin,
                All("F", faceType, All("J", faceType, All("B", faceType,
                    All("eF", Chart(f), All("eJ", Chart(j), Imp(hypotheses, result)))))))))));
    }
}
