using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Unitary;

internal sealed class TensorSquareSingletDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every set of two-by-two complex matrices containing two explicit special unitary matrices, the subspaces of the two-qubit space invariant under every tensor square g tensor g with g in the set are exactly zero, the singlet line, its orthogonal complement of symmetric tensors, which has dimension three, and the whole space; every g tensor g multiplies the singlet by det g.",
        H("Invariant subspaces of the tensor square of two qubits"),
        Blocks(
            Paragraph(Text(
                "V denotes the Euclidean space of complex functions on Fin(2) x Fin(2), the two-qubit "
                + "space with orthonormal basis |00>, |01>, |10>, |11>; x_{ij} is the coordinate of x "
                + "at |ij>. For a two-by-two complex matrix g, kron(g, g) is the Kronecker product of g "
                + "with itself, acting on V as the matrix of g tensor g in this basis.")),
            Node("singlet", "singlet", "The singlet",
                StatementSource.FromAuthor(SingletFormula()), AssessedProvenance.FromRepo(),
                DescribeRole.Definition,
                "The singlet omega is the unnormalized vector |01> - |10> of V: its coordinate at "
                + "|01> is 1, at |10> it is -1, and the other two coordinates are 0."),
            Node("phase", "phaseMatrix", "The diagonal phase matrix",
                StatementSource.FromAuthor(PhaseFormula()), AssessedProvenance.FromRepo(),
                DescribeRole.Definition,
                "phaseMatrix is the diagonal matrix with diagonal entries (3 + 4i)/5 and "
                + "(3 - 4i)/5, two complex numbers of modulus one with product one."),
            Node("rotation", "rotationMatrix", "The real rotation matrix",
                StatementSource.FromAuthor(RotationFormula()), AssessedProvenance.FromRepo(),
                DescribeRole.Definition,
                "rotationMatrix is the rotation of the plane with cosine 3/5 and sine 4/5, viewed as "
                + "a complex matrix."),
            Node("classification", "singlet_invariant_subspaces",
                "Invariant subspaces of the tensor square",
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                DescribeRole.Theorem,
                "In the display, specialUnitaryGroup(Fin(2), C) is the group of two-by-two unitary "
                + "matrices of determinant one, Set(M) is the type of sets of two-by-two complex "
                + "matrices, Submodule(C, V) is the type of complex subspaces of V, 0 is the zero "
                + "subspace, C omega is the line spanned by omega, and the last term V of the "
                + "four-fold disjunction is the whole space. The theorem has six conjuncts. "
                + "phaseMatrix and rotationMatrix are special unitary. For every set S of two-by-two "
                + "complex matrices containing both, a subspace W of V is invariant under kron(g, g) "
                + "for every g in S if and only if W is 0, the line of omega, its orthogonal "
                + "complement, or V. For every two-by-two complex matrix g, kron(g, g) sends omega to "
                + "det(g) omega. A vector lies in the orthogonal complement of omega exactly when its "
                + "coordinates at |01> and |10> agree. The orthogonal complement has dimension three. "
                + "Taking S to be the special unitary group gives the invariant subspaces under all "
                + "of SU(2); the same statement covers the general linear group and the set "
                + "consisting of the two matrices alone.",
                "In coordinates (a, b, c, d) at |00>, |01>, |10>, |11>, the coordinates of "
                + "kron(g, g) applied to omega are 0, g_{00} g_{11} - g_{01} g_{10}, its negative, "
                + "and 0, which gives det(g) omega for every matrix g, unitary or not; the symmetric "
                + "tensors b = c are mapped to symmetric tensors by the same computation. So all four "
                + "subspaces are invariant under every kron(g, g). "
                + "Conversely, kron(phaseMatrix, phaseMatrix) is diagonal with eigenvalues "
                + "alpha = (-7 + 24i)/25 at |00>, 1 at |01> and |10>, and beta = (-7 - 24i)/25 at "
                + "|11>, where alpha, beta and 1 are pairwise distinct. An invariant subspace W "
                + "therefore contains, together with each of its vectors, its |00> part, its |11> "
                + "part and its part in the span of |01> and |10>, obtained as explicit combinations "
                + "of the vector and its images under the first two powers of the diagonal operator. "
                + "The rotation tensor square sends |00> to (9|00> + 12|01> + 12|10> + 16|11>)/25 and "
                + "mixes the weight components, so an invariant W that contains |00> or |11> contains "
                + "every symmetric vector. A case analysis on the weight components of a vector of W "
                + "outside the line of omega, and then of a vector outside the symmetric tensors, "
                + "leaves exactly the four subspaces. The dimension three comes from the orthogonal "
                + "complement of a nonzero vector in the four-dimensional space V.",
                "Neither matrix alone suffices, and the diagonal phases alone do not suffice: every "
                + "matrix diag(z, 1/z) with z nonzero has a tensor square fixing |01> and |10>, so the "
                + "line spanned by |01> is invariant under all of them, and the eigenlines of the "
                + "rotation tensor square are invariant under it. These examples are remarks and are "
                + "not formalised.",
                "For the group SU(2) this is the classical Clebsch-Gordan decomposition of the "
                + "tensor square of the two-dimensional representation into the antisymmetric part, "
                + "spanned by omega, and the irreducible three-dimensional symmetric part; the "
                + "statement that two explicit elements already force the four subspaces, and the "
                + "proof in coordinates, are derived here. Combined with the restriction theorem "
                + "exists_mulEquiv_orthogonal for the line of omega, the isometries of V fixing "
                + "omega correspond to the isometries of the three-dimensional symmetric part with "
                + "the same determinant; that combination is not one of the formal statements of "
                + "this module."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, DescribeRole role, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("tensor-square-singlet-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks([.. paragraphs.Select(static p => Paragraph(Text(p)))]), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Member(Formula x, Formula y) => Rel(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) =>
        new Formula.Logic(x, op, y);
    private static Formula Or(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Or, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ap(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Word(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin2 => Call("Fin", D(2));
    private static Formula Matrices => Call("Matrix", Fin2, Fin2, Complex);
    private static Formula Space => F.Id("V");
    private static Formula Line => Seq(Complex, Sp, Omega);
    private static Formula Complement => Seq(Open, Line, Close, Caret, Grp(Perp));
    private static Formula Kron(Formula g) => Call("kron", g, g);
    private static Formula Coordinate(Formula x, byte i, byte j) => new Formula.Subscript(x, D(i, j));
    private static Formula Gaussian(byte sign) =>
        Frac(Seq(D(3), Sp, sign == 0 ? Plus : Minus, Sp, D(4), F.Id("i")), D(5));

    private static Formula SpaceDefinition => Seq(
        Space, Sp, Eq, Sp, Call("EuclideanSpace", Complex, Seq(Fin2, Sp, Times, Sp, Fin2)),
        Comma, Quad, RowBreak);

    private static Formula Matrix2(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(F.Id("pmatrix")), Sp, a, Sp, Amp, Sp, b, Sp, RowBreak, Sp, c, Sp, Amp, Sp, d, Sp,
        End, Grp(F.Id("pmatrix")));

    private static Formula SingletFormula()
    {
        Formula w = Omega;
        return Disp(Seq(
            SpaceDefinition,
            Omega, Sp, InMacro, Sp, Space, Comma, Quad,
            Equal(Coordinate(w, 0, 1), D(1)), Comma, Quad,
            Equal(Coordinate(w, 1, 0), new Formula.Negate(D(1))), Comma, Quad,
            Equal(Coordinate(w, 0, 0), D(0)), Comma, Quad,
            Equal(Coordinate(w, 1, 1), D(0)), Dot));
    }

    private static Formula PhaseFormula() => Disp(Equal(Word("phaseMatrix"),
        Matrix2(Gaussian(0), D(0), D(0), Gaussian(1))));

    private static Formula RotationFormula() => Disp(Equal(Word("rotationMatrix"),
        Matrix2(Frac(D(3), D(5)), new Formula.Negate(Frac(D(4), D(5))), Frac(D(4), D(5)),
            Frac(D(3), D(5)))));

    private static Formula TheoremFormula()
    {
        Formula g = F.Id("g"), x = F.Id("x"), s = F.Id("S"), w = F.Id("W");
        Formula su = Call("specialUnitaryGroup", Fin2, Complex);
        Formula phase = Word("phaseMatrix"), rotation = Word("rotationMatrix");
        Formula invariant = ForAll("g", s, ForAll("x", w, Member(Ap(Kron(g), x), w)));
        Formula four = Or(Equal(w, D(0)), Or(Equal(w, Line), Or(Equal(w, Complement),
            Equal(w, Space))));
        Formula classification = ForAll("S", Call("Set", Matrices), Implies(Member(phase, s),
            Implies(Member(rotation, s), ForAll("W", Call("Submodule", Complex, Space),
                Logic(invariant, FormulaLogicOperator.Iff, four)))));
        Formula scalar = ForAll("g", Matrices,
            Equal(Ap(Kron(g), Omega), Seq(Call("det", g), Sp, Omega)));
        Formula symmetric = ForAll("x", Space, Logic(Member(x, Complement),
            FormulaLogicOperator.Iff, Equal(Coordinate(x, 0, 1), Coordinate(x, 1, 0))));
        Formula dimension = Equal(Call("finrank", Complex, Complement), D(3));
        return Disp(Seq(
            SpaceDefinition,
            Member(phase, su), Sp, Land, Sp, Member(rotation, su), Sp, Land, RowBreak,
            Open, classification, Close, Sp, Land, RowBreak,
            Open, scalar, Close, Sp, Land, RowBreak,
            Open, symmetric, Close, Sp, Land, Sp, dimension));
    }
}
