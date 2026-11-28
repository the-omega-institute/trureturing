using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ThetaLatticeMinimumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Among planar lattices of any fixed positive covolume, the hexagonal lattice uniquely " +
        "minimizes theta at every positive temperature, up to real orthogonal equivalence and " +
        "the prescribed area scaling.",
        H("The actual lattice minimizers"), Blocks([.. Section0.Entries()])));

    private static class Section0
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("IsHexagonalBasis", "Orthogonal hexagonal images", Definition(),
                "The equality is equality of actual subsets of the complex plane, " +
                "with the origin fixed. Both rotations and reflections are allowed.", true),
            Entry("basis_normSq_scale", "Squared-length scaling", NormScale(),
                "A common real scaling of both basis vectors multiplies every squared length " +
                "by the square of the scale. The identity holds for every real scale, " +
                "including zero and negative scales."),
            Entry("basisTheta_scale", "Theta scaling", ThetaScale(),
                "Apply the squared-length scaling identity to every Gaussian term. " +
                "Scaling both basis vectors by r replaces temperature t by t times r squared."),
            Entry("basis_normalized_area", "Unit-area normalization", NormalizedArea(),
                "Scaling both basis vectors by the reciprocal square root of the positive " +
                "covolume multiplies the determinant by its reciprocal. Its absolute value " +
                "therefore becomes one, for either orientation."),
            Entry("basis_theta_minimum_isometry", "Montgomery's lattice minimum", Minimum(),
                "Normalize both basis vectors by the reciprocal square root of their positive " +
                "covolume A. The normalized basis has area one, and scaling its squared lengths " +
                "changes the temperature to A times t. The reduced theta minimum and pointwise " +
                "orthogonal realization give the lower bound and classify equality exactly by the " +
                "normalized lattice being an orthogonal hexagonal image.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("theta-lattice-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ThetaLatticeMinimum." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), (name == "basis_theta_minimum_isometry"
                ? AssessedProvenance.FromLiterature(Montgomery)
                : AssessedProvenance.FromRepo(Montgomery)),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula Pair => Seq(Z, Times, Z);
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Ex(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula AbsF(Formula a) => new Formula.Absolute(a);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Cast(Formula a) => Seq(Open, a, Colon, C, Close);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Height => Div(Call("sqrt", D(3)), D(2));
    private static Formula Hex(Formula t) => Call("F", t, Div(D(1), D(2)), Height);
    private static Formula Basis(Formula t) => Call("basisTheta", t, V("a"), V("b"));
    private static Formula Hexagonal => Call("IsHexagonalBasis", V("a"), V("b"));
    private static Formula BasisPoint => Add(Mul(Cast(Call("fst", V("v"))), V("a")),
        Mul(Cast(Call("snd", V("v"))), V("b")));
    private static Formula Definition() => All("a", C, All("b", C, Iff(Hexagonal,
        Ex("U", Call("LinearIsometryEquiv", R, C, C), Equal(
            Call("range", Lam("v", Pair, BasisPoint)),
            Call("image", V("U"), Call("range", Lam("v", Pair,
                Call("latticePoint", Div(D(1), D(2)), Height, V("v"))))))))));
    private static Formula Minimum() => All("a", C, All("b", C, All("A", R, All("t", R,
        Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("A")),
            Imp(Equal(AbsF(Sub(Mul(Call("re", V("a")), Call("im", V("b"))),
                Mul(Call("im", V("a")), Call("re", V("b"))))), V("A")),
                Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("t")),
                    And(new Formula.Relation(Hex(Mul(V("A"), V("t"))),
                        FormulaRelationOperator.LessThanOrEqual, Basis(V("t"))),
                        Iff(Equal(Basis(V("t")), Hex(Mul(V("A"), V("t")))),
                            Call("IsHexagonalBasis", Normalize(V("a")), Normalize(V("b"))))))))))));
    private static Formula Normalize(Formula z) => Call("smul",
        Div(D(1), Call("sqrt", V("A"))), z);

    private static Formula Sq(Formula z) => new Formula.Power(z, D(2));
    private static Formula Scale(Formula r, Formula z) => Call("smul", r, z);
    private static Formula PointFor(Formula a, Formula b) =>
        Add(Mul(Cast(Call("fst", V("v"))), a), Mul(Cast(Call("snd", V("v"))), b));
    private static Formula Covolume(Formula a, Formula b) => AbsF(Sub(
        Mul(Call("re", a), Call("im", b)), Mul(Call("im", a), Call("re", b))));
    private static Formula NormScale() => All("r", R, All("a", C, All("b", C, All("v", Pair,
        Equal(Call("normSq", PointFor(Scale(V("r"), V("a")), Scale(V("r"), V("b")))),
            Mul(Sq(V("r")), Call("normSq", PointFor(V("a"), V("b")))))))));
    private static Formula ThetaScale() => All("r", R, All("t", R, All("a", C, All("b", C,
        Equal(Call("basisTheta", V("t"), Scale(V("r"), V("a")), Scale(V("r"), V("b"))),
            Call("basisTheta", Mul(V("t"), Sq(V("r"))), V("a"), V("b")))))));
    private static Formula NormalizedArea() => All("a", C, All("b", C, All("A", R,
        Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("A")),
            Imp(Equal(Covolume(V("a"), V("b")), V("A")),
                Equal(Covolume(Normalize(V("a")), Normalize(V("b"))), D(1)))))));

    }
}
