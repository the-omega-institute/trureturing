using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Unitary;

internal sealed class PointwiseStabilizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/Unitary/PointwiseStabilizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a subspace K of an inner product space E over the real or complex numbers that admits an orthogonal projection, restriction to the orthogonal complement is a group isomorphism from the linear isometries of E fixing K pointwise onto the linear isometries of the orthogonal complement; when E is finite-dimensional it preserves the determinant.",
        H("Isometries fixing a subspace pointwise"),
        Blocks(
            Paragraph(Text(
                "Throughout, k is a field of real or complex scalars (an RCLike field), E is an "
                + "inner product space over k, K is a subspace of E, and K^perp denotes the "
                + "orthogonal complement of K. The linear isometries of E onto itself form a "
                + "group under composition, written LinearIsometryEquiv(E, E).")),
            Node("definition", "pointwiseStabilizer", "The pointwise stabilizer of a subspace",
                StatementSource.FromAuthor(DefinitionFormula()), AssessedProvenance.FromRepo(),
                DescribeRole.Definition,
                "pointwiseStabilizer(K) is the subgroup of the linear isometries U of E onto itself "
                + "with U(x) = x for every vector x of K. It contains the identity, and it is closed "
                + "under composition and inverses: if U and V fix every vector of K, so does U V, "
                + "and U(x) = x gives U^-1(x) = x."),
            Node("restriction", "exists_mulEquiv_orthogonal",
                "Restriction to the orthogonal complement",
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                DescribeRole.Theorem,
                "In the display, MulEquiv(A, B) is the type of group isomorphisms from A onto B, e(U) "
                + "is the isometry of K^perp assigned to U, the equation e(U)(y) = U(y) compares the "
                + "two sides as vectors of E, det(U) is the determinant of U as a linear map of E, "
                + "and det(e(U)) is the determinant of e(U) as a linear map of K^perp. "
                + "The theorem assumes that K has an orthogonal projection, that is, every vector of "
                + "E is the sum of a vector of K and a vector of K^perp; this holds for instance when "
                + "K is complete, in particular when K is finite-dimensional. It states that there is "
                + "a group isomorphism e from pointwiseStabilizer(K) onto the linear isometries of "
                + "K^perp which is restriction, e(U)(y) = U(y) for every U and every y in K^perp, and "
                + "that if E is finite-dimensional then det(U) = det(e(U)) for every U.",
                "An isometry U fixing K pointwise preserves inner products and maps K onto itself, "
                + "so its inverse also fixes K and U maps K^perp onto K^perp. Restriction to K^perp "
                + "is therefore a homomorphism of groups; this step uses no hypothesis on K. "
                + "Injectivity and surjectivity use the decomposition of every vector as k + y with "
                + "k in K and y in K^perp: two elements with the same restriction agree on both "
                + "summands, and an isometry W of K^perp is the restriction of the isometry that is "
                + "the identity on K and W on K^perp, assembled through the orthogonal decomposition "
                + "of E as the orthogonal sum of K and K^perp. "
                + "For the determinant, U(x) - x lies in K^perp for every x, because U(k + y) - "
                + "(k + y) = U(y) - y. Hence U leaves K^perp invariant and induces the identity on the "
                + "quotient E / K^perp, and the determinant of a map preserving a subspace is the "
                + "product of the determinants on the subspace and on the quotient; this gives "
                + "det(U) = det(e(U)) times 1. "
                + "The finite dimension is required of E and not only of K^perp. The determinant of a "
                + "linear map of a space that has no finite basis is 1 by convention, so for an "
                + "infinite-dimensional E and a closed K whose complement K^perp is a line, the "
                + "isometry that is the identity on K and -1 on K^perp has determinant 1 on E and "
                + "-1 on K^perp; this example is a remark and is not formalised. "
                + "The hypothesis that K has an orthogonal projection is equivalent to the "
                + "statement that K and K^perp together span E, which surjectivity needs. "
                + "The result is an elementary fact of linear algebra; it is stated here for every "
                + "RCLike field and for spaces of any dimension."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, DescribeRole role, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("pointwise-stabilizer-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks([.. paragraphs.Select(static p => Paragraph(Text(p)))]), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) =>
        new Formula.Logic(x, op, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ap(Formula f, Formula x) => new Formula.Apply(f, [x]);

    private static Formula K => F.Id("K");
    private static Formula E => F.Id("E");
    private static Formula Field => F.Id("k");
    private static Formula KPerp => Seq(K, Caret, Grp(Perp));
    private static Formula TypeWord => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Stabilizer => Call("pointwiseStabilizer", K);

    private static Formula Instance(Formula item) => Seq(OpenBracket, item, CloseBracket, Comma, Sp);

    /// <summary>The binders of the field, the space and the subspace, with their instances.</summary>
    private static Formula Context(bool projection, Formula body)
    {
        Formula[] prefix =
        [
            Forall, Sp, Field, Colon, Sp, TypeWord, Comma, Sp,
            Instance(Call("RCLike", Field)),
            Forall, Sp, E, Colon, Sp, TypeWord, Comma, Sp,
            Instance(Call("NormedAddCommGroup", E)),
            Instance(Call("InnerProductSpace", Field, E)),
            Forall, Sp, K, Colon, Sp, Call("Submodule", Field, E), Comma, Sp,
        ];
        return projection
            ? Seq([.. prefix, Instance(Call("HasOrthogonalProjection", K)), body])
            : Seq([.. prefix, body]);
    }

    private static Formula DefinitionFormula()
    {
        Formula u = F.Id("U"), x = F.Id("x");
        Formula isometries = Call("LinearIsometryEquiv", E, E);
        return Disp(Context(false, ForAll("U", isometries,
            Logic(Rel(u, FormulaRelationOperator.MemberOf, Stabilizer), FormulaLogicOperator.Iff,
                ForAll("x", K, Equal(Ap(u, x), x))))));
    }

    private static Formula TheoremFormula()
    {
        Formula e = F.Id("e"), u = F.Id("U"), y = F.Id("y");
        Formula target = Call("LinearIsometryEquiv", KPerp, KPerp);
        Formula restriction = ForAll("U", Stabilizer, ForAll("y", KPerp,
            Equal(Ap(Ap(e, u), y), Ap(u, y))));
        Formula determinant = Logic(Call("FiniteDimensional", Field, E), FormulaLogicOperator.Implies,
            ForAll("U", Stabilizer, Equal(Call("det", u), Call("det", Ap(e, u)))));
        return Disp(Context(true, Exists("e", Call("MulEquiv", Stabilizer, target),
            Logic(restriction, FormulaLogicOperator.And, determinant))));
    }
}
