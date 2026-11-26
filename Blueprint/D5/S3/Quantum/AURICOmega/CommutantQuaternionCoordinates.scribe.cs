using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class CommutantQuaternionCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/CommutantQuaternionCoordinates.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/LieTheory/frobenius1878substitutionen");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An irreducible set of linear isometries in dimension at most four whose commutant contains two noncommuting isometries acts by right multiplication by unit quaternions in quaternionic coordinates, in which the given commuting isometries act by left multiplication; the dimension is then four.",
        H("Quaternionic coordinates from a noncommutative commutant"),
        Blocks(
            Node("exists-quaternion-coordinates", "exists_quaternion_coordinates",
                "Quaternionic coordinates from a noncommutative commutant",
                StatementSource.FromAuthor(CoordinatesFormula()), AssessedProvenance.FromRepo(Source),
                "Let E be a finite-dimensional real inner product space with finrank E <= 4, and let U and V be sets of linear isometry equivalences of E. "
                    + "Assume that every real subspace X of E with T x in X for all T in U and all x in X is the zero subspace or all of E, "
                    + "that S * T = T * S for every S in U and every T in V, and that V contains two elements S and T with S * T different from T * S. "
                    + "Then E has dimension four, and for every unit vector e there is a linear isometry equivalence F from E onto the quaternions H with F e = 1 such that "
                    + "for every T in V some quaternion q of norm one satisfies F (T v) = q * F v for all v, and for every S in U some quaternion p of norm one satisfies F (S v) = F v * p for all v. "
                    + "In the formula the isometry is written F and the two sets are written U and V. "
                    + "The argument runs as follows. A symmetric operator commuting with every element of U has an eigenspace invariant under U, which by irreducibility is all of E, so the operator is a scalar. "
                    + "Applied to T + T^-1 for T in V, this writes T as a scalar plus a skew operator commuting with U; applied to anticommutators, it shows that the anticommutator of two such skew operators is a scalar. "
                    + "Two noncommuting elements of V therefore yield, after rescaling and orthogonalization, skew operators J and K commuting with U with J J = -1, K K = -1 and K J = -J K. "
                    + "The space E is nonzero, because any two isometries of the zero space commute; hence E contains a unit vector. For a unit vector e the four vectors e, J e, K e, J (K e) are orthonormal, so E has dimension four, and the isometry F sending them to 1, i, j, k turns J and K into left multiplication by i and j. "
                    + "An element of U commutes with J and K, hence acts by right multiplication by the image of e. "
                    + "For an element T of V, the vectors w with F (T w) = F (T e) * F w form a subspace invariant under U that contains e, hence all of E. "
                    + "The statement asserts existence of such coordinates for each prescribed unit vector e; it asserts no uniqueness. "
                    + "The underlying algebra is classical: the commutant of an irreducible real representation is a division algebra (Schur), and a noncommutative finite-dimensional associative real division algebra is isomorphic to the quaternions (Frobenius).",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("commutant-quaternion-coordinates-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);

    private static Formula CoordinatesFormula()
    {
        Formula e = F.Id("E"), u = F.Id("U"), v = F.Id("V"), x = F.Id("X"), s = F.Id("S"), t = F.Id("T");
        Formula point = F.Id("x"), unit = F.Id("e"), map = F.Id("F"), q = F.Id("q"), p = F.Id("p"), w = F.Id("v");
        Formula finrank = Call("finrank", Reals, e);
        Formula isometries = Call("Set", Call("LinearIsometryEquiv", Reals, e, e));
        Formula dimension = Rel(finrank, FormulaRelationOperator.LessThanOrEqual, D(4));
        Formula irreducible = ForAll("X", Call("Submodule", Reals, e), Implies(
            ForAll("T", u, ForAll("x", x, Rel(At(t, point), FormulaRelationOperator.MemberOf, x))),
            Logic(Equal(x, Named("bot")), FormulaLogicOperator.Or, Equal(x, Named("top")))));
        Formula commute = ForAll("S", u, ForAll("T", v, Equal(Mul(s, t), Mul(t, s))));
        Formula noncommute = Exists("S", v, Exists("T", v,
            Rel(Mul(s, t), FormulaRelationOperator.NotEqual, Mul(t, s))));
        Formula left = ForAll("T", v, Exists("q", Quaternions, And(Equal(Norm(q), D(1)),
            ForAll("v", e, Equal(At(map, At(t, w)), Mul(q, At(map, w)))))));
        Formula right = ForAll("S", u, Exists("p", Quaternions, And(Equal(Norm(p), D(1)),
            ForAll("v", e, Equal(At(map, At(s, w)), Mul(At(map, w), p))))));
        Formula coordinates = ForAll("e", e, Implies(Equal(Norm(unit), D(1)),
            Exists("F", Call("LinearIsometryEquiv", Reals, e, Quaternions),
                And(Equal(At(map, unit), D(1)), And(left, right)))));
        Formula conclusion = And(Equal(finrank, D(4)), coordinates);
        Formula body = ForAllMany(isometries,
            Implies(dimension, Implies(irreducible, Implies(commute, Implies(noncommute, conclusion)))),
            "U", "V");
        return Disp(ForAll("E", TypeStar, Seq(
            OpenBracket, Call("NormedAddCommGroup", e), CloseBracket,
            OpenBracket, Call("InnerProductSpace", Reals, e), CloseBracket,
            OpenBracket, Call("FiniteDimensional", Reals, e), CloseBracket, Comma, Sp,
            body)));
    }
}
