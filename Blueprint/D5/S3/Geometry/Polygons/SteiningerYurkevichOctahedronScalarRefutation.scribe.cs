using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class SteiningerYurkevichOctahedronScalarRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/steiningeryurkevich2026octahedron");
    private const string ScalarQuotation =
        "Printed page 8 reads: “As an application of the above statement, we believe to have found "
        + "a samurai function, that precisely takes its extremes at the optimal solution of the "
        + "Octahedron: Define □(𝒫) to be the side length of the smallest square, into which 𝒫 fits, "
        + "and further define 𝔬(𝒫) ≔ Diam(𝒫)+(23/10)□(𝒫).” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two orthogonal octahedral shadows refute the diameter-plus-square scalar bound.",
        H("The octahedron diameter-plus-square inequality is false"),
        Blocks(
            Node("IsProjection", "Orthonormal-row projection matrices", ProjectionFormula(),
                "Printed page 2 states: “Any such orthogonal projection can be written as M · O, "
                + "for some matrix M ∈ ℝ²ˣ³ satisfying MMᵀ = Id ∈ ℝ²ˣ², and writing M · P ≔ {MP : P ∈ P}.” "
                + "Fin 2 and Fin 3 index the planar and spatial coordinates starting at zero.", true),
            Node("shadow", "Filled Euclidean shadows", ShadowFormula(),
                "Printed page 1 states: “Let O ⊆ ℝ³ be the Octahedron with vertices at "
                + "(e₁,e₂,e₃,−e₁,−e₂,−e₃), where eᵢ denotes the i-th Cartesian unit vector.” "
                + "shadow takes the linear image of its filled convex hull. EuclideanSpace supplies "
                + "the Euclidean norm; WithLp converts between that space and coordinate functions.", true),
            Node("diameter", "Convex-hull diameter", DiameterFormula(),
                "Printed page 4 defines: “Diam(P) is the diameter of P̅, i.e. the largest distance "
                + "between two points of P̅,” with P̅ the convex hull of P. Metric.diam is applied to that hull.", true),
            Node("enclosingSquareLengths", "All enclosing square lengths", EnclosingFormula(),
                ScalarQuotation + "The set displayed here allows every planar rotation R and every translation t. "
                + "Weak enclosing lengths and strict enclosing lengths have the same infimum, "
                + "because each weak enclosure admits an arbitrarily small positive enlargement.", true),
            Node("squareSide", "Smallest enclosing-square side", SquareFormula(),
                ScalarQuotation + "The infimum is over the "
                + "displayed enclosing lengths. On every orthogonal shadow this set is nonempty "
                + "and bounded below by zero; an enclosing square of side two suffices.", true),
            Node("octahedralScalar", "The proposed scalar", ScalarFormula(),
                ScalarQuotation
                + "The coefficient is the fixed real number 23/10.", true),
            Node("projectionValues", "The complete set of projection values", ValuesFormula(),
                "The supremum and infimum on printed page 8 range over every orthogonal projection. "
                + "This set uses all real 2-by-3 matrices satisfying MMᵀ = 1, with no restriction "
                + "to the two projections used in the counterexample.", true),
            Node("claim", "The unnumbered scalar conjecture", IffFormula(F.Id("claim"), ClaimBody()),
                "Printed page 8, section 3, states: “We conjecture that any projection "
                + "of the Octahedron satisfies supπ 𝔬(π(𝐎)) ≤ (3√2/4) infπ 𝔬(π(𝐎)), "
                + "which would yield another proof of the Nieuwland number of the Octahedron.” "
                + "projectionValues encodes its complete projection range; sSup and sInf are real extrema.", true),
            Node("result", "Refutation by a hexagonal shadow", new Formula.Not(Parenthesized(ClaimBody())),
                "The two orthonormal-row matrices yield diameters 2√6/3 and 4√2/3, and smallest "
                + "enclosing-square sides 1+√3/3 and 4/3. Antipodal vertices remove translations; "
                + "unit-circle strip inequalities bound all rotations of the hexagonal shadow. "
                + "The first scalar value exceeds (3√2/4) times the second by more than 9/1250. "
                + "All projection scalar values lie between zero and nine, so the supremum and "
                + "infimum are finite and the displayed inequality fails. The Nieuwland-number "
                + "theorem is a separate assertion.", false, DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-sy2609oct"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("sy-octahedron-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinType(byte n) => Call("Fin", D(n));
    private static Formula Euclidean(byte n) => Call("EuclideanSpace", RealType, FinType(n));
    private static Formula MatrixType(byte m, byte n) => Call("Matrix", FinType(m), FinType(n), RealType);
    private static Formula SetType(Formula type) => Call("Set", type);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula EqF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula SetWhere(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);

    private static Formula ProjectionFormula()
    {
        var m = F.Id("M");
        return All("M", MatrixType(2, 3), IffFormula(Call("IsProjection", m),
            EqF(Multiply(m, App(Qualified("Matrix", "transpose"), m)), D(1))));
    }
    private static Formula ShadowFormula()
    {
        var m = F.Id("M");
        var x = F.Id("x");
        var map = Parenthesized(Seq(F.Id("fun"), Sp, x, Sp, Colon, Sp, Euclidean(3), Sp, Mapsto, Sp,
            App(Qualified("WithLp", "toLp"), D(2),
                App(Qualified("Matrix", "mulVec"), m, App(Qualified("WithLp", "ofLp"), x)))));
        var owner = Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot,
            F.Id("Quantum"), Dot, F.Id("Entanglement"), Dot,
            F.Id("SymmetricBellPolytopeNotCrossPolytope"), Dot, F.Id("crossPolytope"))));
        return All("M", MatrixType(2, 3), EqF(Call("shadow", m),
            App(Qualified("Set", "image"), map, App(owner, D(3)))));
    }
    private static Formula DiameterFormula()
    {
        var p = F.Id("P");
        return All("P", SetType(Euclidean(2)), EqF(Call("diameter", p),
            App(Qualified("Metric", "diam"), Call("convexHull", RealType, p))));
    }
    private static Formula EnclosingFormula()
    {
        var p = F.Id("P");
        var point = F.Id("p");
        var r = F.Id("R");
        var t = F.Id("t");
        var l = F.Id("l");
        var i = F.Id("i");
        var rotation = Parenthesized(Seq(r, Sp, Colon, Sp, MatrixType(2, 2)));
        var coordinate = App(App(Qualified("Matrix", "mulVec"), rotation,
            App(Qualified("WithLp", "ofLp"), Subtract(point, t))), i);
        var containment = All("p", Euclidean(2), Imp(Member(point, p),
            All("i", FinType(2), LeF(new Formula.Absolute(coordinate), new Formula.Fraction(l, D(2))))));
        var lengths = SetWhere("l", RealType, And(LeF(D(0), l),
            Ex("R", App(Qualified("Matrix", "specialOrthogonalGroup"), FinType(2), RealType),
                Ex("t", Euclidean(2), containment))));
        return All("P", SetType(Euclidean(2)), EqF(Call("enclosingSquareLengths", p), lengths));
    }
    private static Formula SquareFormula()
    {
        var p = F.Id("P");
        return All("P", SetType(Euclidean(2)), EqF(Call("squareSide", p),
            Call("sInf", Call("enclosingSquareLengths", p))));
    }
    private static Formula ScalarFormula()
    {
        var p = F.Id("P");
        return All("P", SetType(Euclidean(2)), EqF(Call("octahedralScalar", p),
            Add(Call("diameter", p), Multiply(new Formula.Fraction(D(2, 3), D(1, 0)), Call("squareSide", p)))));
    }
    private static Formula ValuesFormula()
    {
        var r = F.Id("r");
        var m = F.Id("M");
        return EqF(F.Id("projectionValues"), SetWhere("r", RealType,
            Ex("M", MatrixType(2, 3), And(Call("IsProjection", m),
                EqF(r, Call("octahedralScalar", Call("shadow", m)))))));
    }
    private static Formula ClaimBody() => LeF(Call("sSup", F.Id("projectionValues")),
        Multiply(new Formula.Fraction(Multiply(D(3), App(Qualified("Real", "sqrt"), D(2))), D(4)),
            Call("sInf", F.Id("projectionValues"))));
}
