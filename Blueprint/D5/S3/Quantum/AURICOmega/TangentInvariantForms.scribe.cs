using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class TangentInvariantFormsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/TangentInvariantForms.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bilinear forms on the pure quaternions that are invariant under conjugation by unit quaternions: uniqueness up to a factor is equivalent to irreducibility, all conjugations together act irreducibly, and a single rotation through an angle outside the multiples of pi leaves exactly a three-parameter family invariant.",
        H("Invariant bilinear forms on the pure quaternions"),
        Blocks(
            Node("tfae", "invariant_bilinear_tfae",
                "Uniqueness of invariant forms is irreducibility",
                StatementSource.FromAuthor(TfaeFormula()),
                "Let S be a set of unit quaternions, and let a unit quaternion u act on the pure quaternions, those x with re(x) = 0, by the conjugation x -> u x star(u), a rotation of this three-dimensional real space. A real bilinear form B on the quaternions is called invariant on the pure quaternions when B(u x star(u), u y star(u)) = B(x, y) for all u in S and all pure x, y. The theorem states that the following three conditions are equivalent: (1) every invariant bilinear form is, on the pure quaternions, a real multiple c <x, y> of the inner product; (2) the same holds for every invariant symmetric bilinear form; (3) every subspace W of the quaternions that consists of pure quaternions and is mapped into itself by the conjugations by S is either zero or contains every pure quaternion. In the display <x, y> is the real inner product of the quaternions and TFAE states that the listed propositions are pairwise equivalent; nothing is assumed of S.",
                DescribeRole.Theorem,
                "(1) implies (2) trivially. (3) implies (1): on the pure quaternions B(x, y) = <A x, y> for a linear map A of the pure quaternions into themselves, and invariance means that A commutes with every conjugation by S. The pure quaternions have dimension three, which is odd, so A has a real eigenvalue c; its eigenspace is invariant and nonzero, so by (3) it contains every pure quaternion, and then B(x, y) = c <x, y> there. (2) implies (3): the orthogonal projection P onto an invariant subspace W commutes with the conjugations, so <P x, y> is an invariant symmetric form; by (2) it equals c <x, y> on the pure quaternions, and evaluating at a nonzero vector of W gives c = 1, so W contains every pure quaternion. "
                    + "This is Schur's lemma for real representations, in the classical form that an irreducible real representation of odd dimension is of real type: its commuting operators are real scalars. The eigenvalue in odd dimension comes from the odd-degree root theorem for the real numbers."),
            Node("all-conjugations", "conj_invariant_bilinear_eq_smul_inner",
                "Forms invariant under all conjugations",
                StatementSource.FromAuthor(AllConjugationsFormula()),
                "A real bilinear form B on the quaternions that is invariant on the pure quaternions under the conjugation by every unit quaternion is, on the pure quaternions, a real multiple c <x, y> of the inner product.",
                DescribeRole.Theorem,
                "This is condition (1) of the preceding equivalence for the set of all unit quaternions, and condition (3) holds for that set: a nonzero invariant subspace W contains a nonzero pure quaternion w, any two unit quaternions with the same real part are conjugate, so w / |w| is conjugate to x / |x| for every nonzero pure quaternion x, and x is then a real multiple of a conjugate of w, which lies in W. The full conjugation group is the rotation group of the three-dimensional space of pure quaternions."),
            Node("one-rotation", "conj_invariant_bilinear_iff",
                "Forms invariant under one rotation",
                StatementSource.FromAuthor(OneRotationFormula()),
                "Let u be a unit quaternion with re(u) nonzero and im(u) nonzero, and write n = im(u). A real bilinear form B on the quaternions is invariant on the pure quaternions under the conjugation by u if and only if there are real numbers a, b, c with B(x, y) = a <x, y> + b <n, x> <n, y> + c <n, x y> for all pure x, y. The coefficients alpha, beta, gamma of the Lean statement are written a, b, c in the display. For pure x and y one has x y = -<x, y> + x cross y, so <n, x y> = <n, x cross y>; the third form is the triple product with n and is antisymmetric, and the invariant symmetric forms are exactly those with c = 0, a two-dimensional family.",
                DescribeRole.Theorem,
                "The conjugation by u = cos t + sin t m, with m a unit pure quaternion, is the rotation about the axis m through the angle 2t, and the hypotheses say that 2t is not a multiple of pi. Each of the three forms is invariant because u commutes with n. Conversely, a unit quaternion q carrying i to n / |n| reduces the problem to the axis i, where the invariance equations on the basis i, j, k force the matrix of the form on the pure quaternions to commute with a rotation through an angle outside the multiples of pi about i; such matrices are spanned by the identity, the projection onto i and the cross product with i, because the rotation has the distinct eigenvalues 1, e^(2it) and e^(-2it). "
                    + "Both hypotheses are needed; the following counts were obtained numerically and are not formalized. When re(u) = 0 the conjugation is a half-turn, and its invariant bilinear forms on the pure quaternions form a five-dimensional space. When im(u) = 0, that is u = 1 or u = -1, the conjugation is the identity and all bilinear forms, a nine-dimensional space, are invariant. The classification is an instance of the classical description of the commutant of a rotation in three dimensions."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, string prose, DescribeRole role,
        params string[] more) =>
        Describe.Lean(DescribeId.Create("tangent-invariant-forms-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(prose)), .. more.Select(paragraph => Paragraph(Text(paragraph)))]), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(n => new Formula.BoundVariable(FormulaIdentifier.Create(n), domain))], body);
    private static Formula ExistsMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. names.Select(n => new Formula.BoundVariable(FormulaIdentifier.Create(n), domain))], body);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Forms => Call("LinearMap", Reals, Quaternions, Call("LinearMap", Reals, Quaternions, Reals));
    private static Formula Inner(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle);
    private static Formula Pure(Formula x) => Equal(Call("re", x), D(0));
    private static Formula Conj(Formula u, Formula x) => Mul(Mul(u, x), Call("star", u));

    /// <summary>For all pure x, y: hypothesis-free conclusion `body`.</summary>
    private static Formula ForAllPure(Formula body) =>
        ForAllMany(Quaternions, Implies(Pure(F.Id("x")), Implies(Pure(F.Id("y")), body)), "x", "y");

    private static Formula Invariance(Formula b, Formula u) =>
        ForAllPure(Equal(Call("B", Conj(u, F.Id("x")), Conj(u, F.Id("y"))), Call("B", F.Id("x"), F.Id("y"))));

    private static Formula ScalarMultiple() =>
        Exists("c", Reals, ForAllPure(Equal(Call("B", F.Id("x"), F.Id("y")),
            Mul(F.Id("c"), Inner(F.Id("x"), F.Id("y"))))));

    private static Formula TfaeFormula()
    {
        Formula b = F.Id("B"), u = F.Id("u"), w = F.Id("W"), s = F.Id("S");
        Formula invariantUnderS = ForAll("u", s, Invariance(b, u));
        Formula first = ForAll("B", Forms, Implies(invariantUnderS, ScalarMultiple()));
        Formula symmetric = ForAllMany(Quaternions,
            Equal(Call("B", F.Id("x"), F.Id("y")), Call("B", F.Id("y"), F.Id("x"))), "x", "y");
        Formula second = ForAll("B", Forms, Implies(symmetric, Implies(invariantUnderS, ScalarMultiple())));
        Formula pureSubspace = ForAll("v", w, Pure(F.Id("v")));
        Formula invariantSubspace = ForAll("u", s, ForAll("v", w,
            Rel(Conj(u, F.Id("v")), FormulaRelationOperator.MemberOf, w)));
        Formula trivialOrAll = Logic(Equal(w, Perp), FormulaLogicOperator.Or,
            ForAll("x", Quaternions, Implies(Pure(F.Id("x")),
                Rel(F.Id("x"), FormulaRelationOperator.MemberOf, w))));
        Formula third = ForAll("W", Call("Submodule", Reals, Quaternions),
            Implies(pureSubspace, Implies(invariantSubspace, trivialOrAll)));
        return Disp(ForAll("S", Call("Set", Units),
            Call("TFAE", Seq(OpenBracket, first, Comma, Sp, second, Comma, Sp, third, CloseBracket))));
    }

    private static Formula AllConjugationsFormula()
    {
        Formula b = F.Id("B"), u = F.Id("u");
        return Disp(ForAll("B", Forms,
            Implies(ForAll("u", Units, Invariance(b, u)), ScalarMultiple())));
    }

    private static Formula OneRotationFormula()
    {
        Formula b = F.Id("B"), u = F.Id("u"), x = F.Id("x"), y = F.Id("y");
        Formula n = Call("im", u);
        Formula family = Add(Add(
                Mul(F.Id("a"), Inner(x, y)),
                Mul(Mul(F.Id("b"), Inner(n, x)), Inner(n, y))),
            Mul(F.Id("c"), Inner(n, Mul(x, y))));
        Formula right = ExistsMany(Reals, ForAllPure(Equal(Call("B", x, y), family)), "a", "b", "c");
        return Disp(ForAll("u", Units,
            Implies(Rel(Call("re", u), FormulaRelationOperator.NotEqual, D(0)),
                Implies(Rel(n, FormulaRelationOperator.NotEqual, D(0)),
                    ForAll("B", Forms,
                        Logic(Invariance(b, u), FormulaLogicOperator.Iff, right))))));
    }
}
