using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class FiskToeplitzRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/FiskToeplitzRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/fisk2008determinants");
    private const string Question =
        "Suppose f∈P⁺₂, and write f = ∑ f_i(x)y^i. Form the infinite matrix";
    private const string Conclusion =
        "Show that the resulting matrix is totally stable. That is, every minor is a stable polynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive upper bivariate polynomial has a non-Hurwitz coefficient-Toeplitz minor.",
        H("A counterexample to Fisk's Question 10"),
        Blocks(
            Node("Upper", "Upper bivariate polynomials", UpperFormula(),
                "PDF p. 1: “All polynomials f(x₁,…,x_d) with real coefficients such that "
                + "f(σ₁,…,σ_d)≠0 for all σ₁,…,σ_d in the open upper half plane.” "
                + "Here d=2. The carrier is Polynomial (Polynomial ℝ), with x in the "
                + "coefficient ring and y outermost. Polynomial.eval₂ embeds the real "
                + "coefficients into ℂ and evaluates at x and y.",
                AssessedProvenance.FromLiterature(Source)),
            Node("PositiveUpper", "Positive coefficients on the support", PositiveFormula(),
                "PDF p. 1: “P⁺_d = all polynomials in U_d with all positive coefficients.” "
                + "Every nonzero coefficient (f.coeff j).coeff i is strictly positive; "
                + "absent monomials have coefficient zero. The condition Upper excludes the zero input.",
                AssessedProvenance.FromLiterature(Source)),
            Node("HurwitzStable", "Closed left half-plane roots", StableFormula(),
                "PDF p. 1: “H₁ = all polynomials with all roots in the closed left half plane.” "
                + "The real coefficients are mapped to ℂ before taking Polynomial.roots. "
                + "The zero polynomial has the empty root multiset, so structural zero minors "
                + "are included. The counterexample minor is nonzero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("toeplitz", "The coefficient matrix (5)", ToeplitzFormula(),
                "Question 10, PDF p. 4: “" + Question + "”. "
                + "Matrix (5) has f₀,f₁,f₂,… in its first row, with each next row shifted "
                + "one column to the right and zeros below the diagonal. Rows and columns "
                + "are indexed by ℕ from zero. Polynomial.coeff is zero beyond the degree.",
                AssessedProvenance.FromLiterature(Source)),
            Node("minor", "Ordered finite minors", MinorFormula(),
                "Question 10, PDF p. 4: “" + Conclusion + "” "
                + "The polynomial is the determinant of the selected submatrix. "
                + "StrictMono row and column maps in claim preserve the source's order "
                + "and determinant sign. The size-zero determinant is one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Question 10", Eqn(Op("claim"), Parenthesized(ClaimBody())),
                "Question 10, PDF p. 4: “" + Question + "”. Matrix (5) is toeplitz. “"
                + Conclusion + "” The quantifiers range over every real bivariate polynomial, "
                + "every natural size and every two strictly increasing maps Fin n → ℕ. "
                + "The roots must have nonpositive real part.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "Question 10 is false", Seq(Neg, Sp, Parenthesized(ClaimBody())),
                "Take f=(4x+y+1)(x+y+4). Each affine factor has positive imaginary part "
                + "when x and y do, and all six nonzero coefficients are positive. "
                + "Rows 0,…,4 and columns 1,…,5 give a tridiagonal minor with determinant "
                + "5(x+1)(21x²+33x+21)(13x²−x+13). The complex number "
                + "(1+15i√3)/26 is a root with real part 1/26. Thus this nonzero minor "
                + "fails HurwitzStable. The five-by-five determinant factors as "
                + "b(b²−a)(b²−3a), where a=4x²+17x+4 and b=5x+5.",
                AssessedProvenance.FromRepo(Source), true))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, bool theorem = false) => Describe.Lean(
            DescribeId.Create("fisk-toeplitz-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            provenance,
            Blocks(Paragraph(DefinitionDsl.Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            theorem ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("fisk10-toeplitz"),
                ResolutionKind.Refuted) : null);

    private static Formula Id(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula Qualified(string owner, string member) => Seq(Op(owner), Dot, Op(member));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] args)
    {
        var items = new List<Formula>();
        foreach (var arg in args)
        {
            if (items.Count > 0) items.Add(Comma);
            items.Add(arg);
        }
        return Seq(function, Parenthesized(Seq([.. items])));
    }
    private static Formula Var(string name, Formula type) => Parenthesized(Seq(Id(name), Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Var(name, type), Comma, Sp, body);
    private static Formula Eqn(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Neq(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.NotEqual, rhs);
    private static Formula Arrow(Formula lhs, Formula rhs) =>
        new Formula.Logic(lhs, FormulaLogicOperator.Implies, rhs);
    private static Formula And(Formula lhs, Formula rhs) =>
        new Formula.Logic(lhs, FormulaLogicOperator.And, rhs);
    private static Formula Member(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.MemberOf, rhs);
    private static Formula Leq(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs);
    private static Formula Less(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.LessThan, rhs);
    private static Formula Nat => Op("Nat");
    private static Formula Real => Op("Real");
    private static Formula Complex => Op("Complex");
    private static Formula Poly => Call("Polynomial", Real);
    private static Formula BiPoly => Call("Polynomial", Poly);
    private static Formula Index => new Formula.TypeArrow(Call("Fin", Id("n")), Nat);
    private static Formula Coeff(Formula p, Formula i) => App(Seq(Parenthesized(p), Dot, Op("coeff")), i);
    private static Formula Cast => Call("algebraMap", Real, Complex);
    private static Formula Eval2 => new Formula.Subscript(Op("eval"), D(2));
    private static Formula Eval2RingHom => Seq(Eval2, Op("RingHom"));
    private static Formula UpperFormula()
    {
        var eval = App(Seq(Id("f"), Dot, Eval2),
            App(Seq(Op("Polynomial"), Dot, Eval2RingHom), Cast, Id("x")), Id("y"));
        var upper = Qualified("UpperHalfPlane", "upperHalfPlaneSet");
        return All("f", BiPoly, Eqn(Call("Upper", Id("f")), Parenthesized(
            All("x", Complex, All("y", Complex,
                Arrow(Member(Id("x"), upper), Arrow(Member(Id("y"), upper), Neq(eval, D(0)))))))));
    }
    private static Formula PositiveFormula()
    {
        var coeff = Coeff(Coeff(Id("f"), Id("j")), Id("i"));
        return All("f", BiPoly, Eqn(Call("PositiveUpper", Id("f")), Parenthesized(
            And(Call("Upper", Id("f")), All("i", Nat, All("j", Nat,
                Arrow(Neq(coeff, D(0)), Less(D(0), coeff))))))));
    }
    private static Formula StableFormula()
    {
        var mapped = App(Seq(Id("p"), Dot, Op("map")), Cast);
        return All("p", Poly, Eqn(Call("HurwitzStable", Id("p")), Parenthesized(
            All("z", Complex, Arrow(Member(Id("z"), Seq(Parenthesized(mapped), Dot, Op("roots"))),
                Leq(Seq(Id("z"), Dot, Op("re")), D(0)))))));
    }
    private static Formula ToeplitzFormula() => All("f", BiPoly,
        Eqn(Call("toeplitz", Id("f")), Parenthesized(Seq(
            LambdaLower, Sp, Var("r", Nat), Var("c", Nat), Mapsto, Sp,
            Op("if"), Sp, Leq(Id("r"), Id("c")), Sp, Op("then"), Sp,
            Coeff(Id("f"), Seq(Id("c"), Minus, Id("r"))), Sp, Op("else"), Sp, D(0)))));
    private static Formula MinorFormula()
    {
        var entry = Call("toeplitz", Id("f"), App(Id("R"), Id("i")), App(Id("C"), Id("j")));
        var matrix = Parenthesized(Seq(LambdaLower, Sp, Var("i", Call("Fin", Id("n"))),
            Var("j", Call("Fin", Id("n"))), Mapsto, Sp, entry));
        return All("f", BiPoly, All("n", Nat, All("R", Index, All("C", Index,
            Eqn(Call("minor", Id("f"), Id("n"), Id("R"), Id("C")),
                App(Qualified("Matrix", "det"), matrix))))));
    }
    private static Formula ClaimBody()
    {
        var stable = Call("HurwitzStable", Call("minor", Id("f"), Id("n"), Id("R"), Id("C")));
        var ordered = Arrow(Call("StrictMono", Id("R")), Arrow(Call("StrictMono", Id("C")), stable));
        var minors = All("n", Nat, All("R", Index, All("C", Index, ordered)));
        return All("f", BiPoly, Arrow(Call("PositiveUpper", Id("f")), minors));
    }
}
