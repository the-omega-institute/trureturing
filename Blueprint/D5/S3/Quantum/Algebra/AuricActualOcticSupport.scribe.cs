using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class AuricActualOcticSupportDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string names, Formula type, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse())
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
        return body;
    }
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) =>
        new Formula.Logic(Seq(Open, x, Close), op, Seq(Open, y, Close));
    private static Formula And(params Formula[] xs) =>
        xs.Reverse().Aggregate((x, y) => Logic(y, FormulaLogicOperator.And, x));
    private static Formula Imp(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Instance(string name, params Formula[] xs) => Seq(OpenBracket, Call(name, xs), CloseBracket, Sp);

    private static Formula Statement()
    {
        var f = V("F"); var d = V("D"); var k = V("K"); var l = V("L");
        var w = V("W"); var a = V("a"); var e = V("e"); var n = V("n"); var m = V("N");
        var omega = Call("AlgHom", f, d, k);
        var coordinates = Call("Map", omega, k);
        var support = And(Call("StronglyConnected", Call("nonzeroSupport", m)),
            Call("StronglyConnected", Call("nonzeroSupport", Call("map", Call("algebraMap", k, l), m))),
            Call("Irreducible", Call("det", Call("rowMatrix", Call("map", Call("algebraMap", k, l), m)))),
            Call("Irreducible", Call("det", Call("diagonalMatrix", Call("map", Call("algebraMap", k, l), m)))));
        var definitions = All("n", Call("LinearMap", k, coordinates, coordinates),
            Imp(Equal(n, Call("compose", Call("linear", e), Call("baseChange", k, Call("actualOperator", w, a)),
                Call("linear", Call("inverse", e)))),
            All("N", Call("Matrix", omega, omega, k), Imp(Equal(m, Call("toMatrix", n)), support))));
        var splitting = Some("e", Call("AlgEquiv", k, Call("Tensor", f, k, d), coordinates), And(
            All("c", k, All("z", d, All("sigma", omega,
                Equal(Call("apply", e, Call("tensor", V("c"), V("z")), V("sigma")),
                    Mul(V("c"), Call("apply", V("sigma"), V("z"))))))), definitions));
        var premises = And(Equal(Call("finrank", f, d), D(8)), Equal(Call("finrank", f, w), D(4)),
            Equal(Call("Idealizer", f, d, w), Call("range", Call("algebraMap", f, d))),
            Seq(Neg, Sp, Rel(a, FormulaRelationOperator.MemberOf, Call("quotientSet", w))));
        return All("F D K L", V("Type"), Seq(
            Instance("Field", f), Instance("Field", d), Instance("Field", k), Instance("Field", l),
            Instance("Algebra", f, d), Instance("Algebra", f, k), Instance("Algebra", d, k),
            Instance("Algebra", k, l), Instance("IsScalarTower", f, d, k),
            Instance("FiniteDimensional", f, d), Instance("CharZero", f),
            Instance("FiniteDimensional", f, k), Instance("Normal", f, k),
            All("W", Call("Submodule", f, d), All("a", d, Imp(premises, splitting)))));
    }

    private static Formula OriginalPolynomialStatement(bool overOriginalField)
    {
        var f = V("F"); var d = V("D"); var k = V("K"); var l = V("L");
        var w = V("W"); var a = V("a");
        var assumptions = And(Equal(Call("finrank", f, d), D(8)), Equal(Call("finrank", f, w), D(4)),
            Equal(Call("Idealizer", f, d, w), Call("range", Call("algebraMap", f, d))),
            Seq(Neg, Sp, Rel(a, FormulaRelationOperator.MemberOf, Call("quotientSet", w))));
        var coefficientMap = overOriginalField ? Call("algebraMap", f, l)
            : Call("compose", Call("algebraMap", k, l), Call("algebraMap", f, k));
        var result = Call("Irreducible", Call("map", coefficientMap,
            Call("obstructionPolynomial", w, V("bD"), V("bW"), V("bQ"))));
        return All("F D K L", V("Type"), Seq(
            Instance("Field", f), Instance("Field", d), Instance("Field", k), Instance("Field", l),
            Instance("Algebra", f, d), Instance("Algebra", f, k), Instance("Algebra", d, k),
            Instance("Algebra", overOriginalField ? f : k, l), Instance("IsScalarTower", f, d, k),
            Instance("FiniteDimensional", f, d), Instance("CharZero", f),
            Instance("FiniteDimensional", f, k), Instance("Normal", f, k),
            All("W", Call("Submodule", f, d), All("bD", Call("Basis", Call("Fin", D(8)), f, d),
            All("bW", Call("Basis", Call("Fin", D(4)), f, w),
            All("bQ", Call("Basis", Call("Fin", D(4)), f, Call("Quotient", d, w)),
            All("a", d, Imp(assumptions, result))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directed support and parameter determinants of the actual octic window operator.", H("Actual octic support connectivity"),
        Blocks(
            Paragraph(Text(
                "F has characteristic zero, D/F has degree eight, and W is an arbitrary four dimensional "
                + "F subspace whose multiplication idealizer is exactly F. The element a lies outside "
                + "Q(W), the set of quotients of elements of W with nonzero denominator. K/F is a finite "
                + "normal extension containing the same D, and L/K is any field extension. "
                + "Omega consists of the literal F algebra embeddings of D into K.")),
            Paragraph(Text(
                "nonzeroSupport(N) has an arrow from sigma to tau exactly when N(sigma,tau) is nonzero. "
                + "StronglyConnected means that every ordered pair is joined by a finite directed path, "
                + "allowing a path of length zero. The matrix map applies the coefficient embedding K to L "
                + "to each entry; it leaves all embedding labels fixed. The constrained n and N express "
                + "the let bindings defining the original inverse-obstruction matrix.")),
            Describe.Lean(DescribeId.Create("actual-general43-2-support"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/AuricActualOcticSupport.general43_2_support"),
                H("Strong connectivity and irreducibility over every coefficient extension"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical evaluation splitting sends c tensor d to the function sigma maps to "
                    + "c times sigma(d). The strict projection rank inequality gives 2 rho(S) at least "
                    + "card(S)+1 for every nonempty proper S. Rank-nullity for the same actual operator, "
                    + "whose kernel and image are the split window, bounds 2 rho(S) above by card(S) "
                    + "plus rank N[S,S complement]. Every such crossing block therefore has positive rank. "
                    + "If sigma cannot reach tau, let S consist of the vertices that can reach tau. "
                    + "It contains tau and excludes sigma. Every entry from S complement to S is zero, "
                    + "since a nonzero entry would extend a path to tau. This contradicts the positive "
                    + "crossing rank for S complement. Finally the coefficient embedding is injective, "
                    + "so every edge and every finite path remains present over L. "
                    + "The fixed-matrix row-parameter theorem now proves irreducibility of the determinant "
                    + "of I plus diag(x) times the coefficient image of this same actual N over L. "
                    + "The diagonal-parameter theorem proves irreducibility of det(diag(y)+N) for that "
                    + "same coefficient image, with the same literal embedding labels. "
                    + "No connectivity hypothesis is added to the original window telescope. The theorem "
                    + "does not identify this polynomial with the original multiplication obstruction "
                    + "in its chosen original basis; that normalization and coordinate bridge remain separate. "
                    + "The reciprocal determinant identity applies to this same N in any commutative "
                    + "coefficient ring with unit coordinates, including the Laurent polynomial ring."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-original-polynomial-irreducible"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/AuricActualOcticSupport.general43_2_original_polynomial"),
                H("The original obstruction polynomial over every L/K"),
                StatementSource.FromAuthor(Disp(OriginalPolynomialStatement(false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The polynomial is the original determinant in the arbitrary bases bD, bW and bQ, "
                    + "not a polynomial with independent matrix entries. The normalization theorem uses "
                    + "the same actual N supplied by general43_2_support. The invertible affine substitution "
                    + "extends coefficient by coefficient from K to every L/K, together with its inverse. "
                    + "Its image of the original polynomial is a nonzero constant times the fixed row "
                    + "determinant, using the determinant identity to exchange the two product orders. "
                    + "Irreducibility therefore transfers back to the original polynomial over L. "
                    + "This theorem quantifies over extensions of K and supplies the common-overfield "
                    + "step in the original-field geometric irreducibility theorem below. "
                    + "The source atom also retains its separate quotient-density and classification clauses."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-original-polynomial-geometric-irreducibility"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/AuricActualOcticSupport.general43_2_original_geometric_irreducibility"),
                H("The original obstruction polynomial over every L/F"),
                StatementSource.FromAuthor(Disp(OriginalPolynomialStatement(true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "L is an arbitrary field extension of F; no embedding of K into L is assumed. "
                    + "Embed the finite algebraic extension K/F into an algebraic closure A of L as an "
                    + "F algebra. The F to K to A and F to L to A coefficient maps agree with the same "
                    + "F algebra structure on A. Apply the preceding theorem over A, retaining its same "
                    + "actual splitting, matrix, original bases and polynomial. A unit polynomial over A "
                    + "has a unit constant coefficient and nilpotent other coefficients. Coefficient "
                    + "injectivity reflects both conditions to L, so the polynomial coefficient map "
                    + "reflects units. Mathlib's Irreducible.of_map then descends irreducibility to L. "
                    + "This proves geometric irreducibility of the original f_W, without identifying "
                    + "an arbitrary L/F with an extension of K. Quotient density and the remaining "
                    + "classification clauses are separate obligations."))),
                DescribeRole.Theorem))));
}
