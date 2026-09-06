using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintWignerCriticalGeometryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact ququint Wigner zeros, tangent dimension, and critical gradient.",
        H("Ququint Wigner Critical Geometry"),
        Blocks(
            Claim("State", "The state space",
                Seq(Name("State"), Eq, Call(Name("EuclideanSpace"), ComplexType, Fin(5))),
                "State is the complex Euclidean space on Fin 5, with its L2 norm.", DescribeRole.Definition),
            Paragraph(Text("radical denotes QuquintCertificateData.radical. Its definition, square, "
                + "quartic identity and bounds are given in QuquintCertificateData.")),
            Claim("zeta", "The fifth root of unity",
                Seq(Name("zeta"), Eq, Call(Qualified("Complex", "exp"),
                    Seq(D(2), Cdot, Cast(Qualified("Real", "pi"), ComplexType), Cdot,
                        Qualified("Complex", "I"), Slash, D(5)))),
                "The phase convention uses exp of two pi times the imaginary unit divided by five.",
                DescribeRole.Definition),
            Claim("phasePoint", "The phase-point kernel",
                Seq(Forall, Sp, Q, Sp, P, Sp, X, Sp, Y, Colon, Fin(5), Comma,
                    Call(Name("phasePoint"), Q, P, X, Y), Eq,
                    Call(Name("ite"), Equal(Seq(ModFive(X), Plus, ModFive(Y)), Seq(D(2), Cdot, ModFive(Q))),
                        Power(Name("zeta"), Call(Name("val"),
                            Seq(ModFive(P), Cdot, Parenthesized(Seq(ModFive(X), Minus, ModFive(Y)))))), D(0))),
                "The condition and exponent arithmetic are in ZMod 5. val converts the exponent to a natural number. "
                    + "This is the paper's phase-point convention after exchanging the labels p and q.",
                DescribeRole.Definition, literature: true),
            Claim("wigner", "The Wigner quadratic form",
                Seq(Forall, Sp, V, Colon, Name("State"), Comma, Forall, Sp, Q, Sp, P, Colon, Fin(5), Comma,
                    Call(Name("wigner"), V, Q, P), Eq,
                    Call(Qualified("Complex", "re"), Pair(OfLp(V), MulVec(Call(Name("phasePoint"), Q, P), OfLp(V)))),
                    Slash, D(5)),
                "The real part of the Hermitian phase-point pairing is divided by five.",
                DescribeRole.Definition, literature: true),
            Claim("lOne", "The Wigner norm sum",
                Seq(Forall, Sp, V, Colon, Name("State"), Comma, Call(Name("lOne"), V), Eq,
                    SumOver(Q, Fin(5)), SumOver(P, Fin(5)), Call(Name("abs"), Call(Name("wigner"), V, Q, P))),
                "The two finite sums include all twenty-five phase points.", DescribeRole.Definition),
            Claim("psi", "The specified ququint state",
                Seq(Name("psi"), Eq, Call(Qualified("WithLp", "toLp"), D(2),
                    Seq(Parenthesized(Seq(D(1), Slash, Cast(Seq(Sqrt, Grp(D(5))), ComplexType))), Cdot, PhaseVector))),
                "Appendix E, equation E.3a, specifies this normalized five-component state.",
                DescribeRole.Definition, literature: true),
            Claim("zeroPoints", "The vanishing phase points",
                Seq(Name("zeroPoints"), Eq, Call(Qualified("Finset", "filter"),
                    Parenthesized(Seq(Cast(QP, PointType), Mapsto,
                        Equal(Call(Name("wigner"), Name("psi"), Projection(QP, 1), Projection(QP, 2)), D(0)))),
                    Qualified("Finset", "univ"))),
                "Filtering the finite phase plane by the vanishing predicate defines zeroPoints.", DescribeRole.Definition),
            Claim("zero_points_eq", "The exact zero set",
                Seq(Name("zeroPoints"), Eq, ZeroSet),
                "The exact Wigner table determines these five points."),
            Claim("zero_points_card", "The zero-set cardinality",
                Seq(Call(Qualified("Finset", "card"), Name("zeroPoints")), Eq, D(5)),
                "The five displayed points are distinct."),
            Claim("lOne_psi", "The norm sum at the specified state",
                Seq(Call(Name("lOne"), Name("psi")), Eq, D(1), Plus, D(2), Cdot, Sqrt, Grp(D(5)), Slash, D(5)),
                "The exact twenty-five-entry Wigner table gives this value."),
            Claim("gradient", "The signed phase-point sum",
                Seq(Name("gradient"), Eq, SumOver(Q, Fin(5)), SumOver(P, Fin(5)),
                    SignedPhase(Q, P)),
                "The SignType coefficient is explicitly coerced to the complex scalar field.", DescribeRole.Definition),
            Claim("tangent", "The constrained real tangent space",
                Seq(Forall, Sp, V, Colon, Name("State"), Comma,
                    Member(V, Name("tangent")), Iff,
                    Parenthesized(Seq(Equal(Pair(OfLp(Name("psi")), OfLp(V)), D(0)), Sp, Land, Sp,
                        Parenthesized(Seq(Forall, Sp, QP, Colon, PointType, Comma,
                            Member(QP, Name("zeroPoints")), Implies,
                            Equal(Call(Qualified("Complex", "re"), Pair(OfLp(Name("psi")),
                                MulVec(Call(Name("phasePoint"), Projection(QP, 1), Projection(QP, 2)), OfLp(V)))), D(0))))))),
                "tangent is the real Submodule of State cut out by complex orthogonality to psi "
                    + "and the five real phase-point pairing constraints.", DescribeRole.Definition),
            Claim("phases", "The component phases",
                Seq(Name("phases"), Eq, PhaseVector),
                "This vector has type Fin 5 to the complex numbers.", DescribeRole.Definition),
            Claim("gauge", "Phase-adjusted real coordinates",
                Seq(Forall, Sp, U, Colon, RealCoordinates(10), Comma, Call(Name("gauge"), U), Eq,
                    Call(Qualified("WithLp", "toLp"), D(2), Parenthesized(Seq(Cast(I, Fin(5)), Mapsto,
                        Call(Name("phases"), I), Cdot, Call(Qualified("Complex", "mk"),
                            Call(U, Call(Qualified("Fin", "castAdd"), D(5), I)),
                            Call(U, Call(Qualified("Fin", "natAdd"), D(5), I))))))),
                "The first five real coordinates and the last five imaginary coordinates are multiplied by phases.",
                DescribeRole.Definition),
            Claim("basisMatrix", "The exact real basis matrix",
                Seq(Name("basisMatrix"), Colon, MatrixType(10, 4, RealType), Eq, BasisRows),
                "The ten rows are listed in the real-then-imaginary order used by gauge. "
                    + "The checked constraint, selector, and elimination identities establish a basis of tangent.",
                DescribeRole.Definition),
            Claim("tangentEquiv", "The real linear coordinate equivalence",
                Seq(Name("tangentEquiv"), Colon, RealCoordinates(4), Equiv, Underscore, Grp(Name("l")),
                    OpenBracket, RealType, CloseBracket, Name("tangent"), Comma,
                    Parenthesized(Seq(Forall, Sp, A, Colon, RealCoordinates(4), Comma,
                        Cast(Call(Name("tangentEquiv"), A), Name("State")), Eq,
                        Call(Name("gauge"), MulVec(Name("basisMatrix"), A)))), Sp, Land, Sp,
                    Parenthesized(Seq(Forall, Sp, V, Colon, Name("tangent"), Comma,
                        Call(Qualified("tangentEquiv", "symm"), V), Eq,
                        Vector(Ungauged("re", 3), Ungauged("re", 4), Ungauged("im", 3), Ungauged("im", 4))))),
                "The forward map carries the displayed state into tangent. The inverse removes the phases "
                    + "and takes real coordinates 3 and 4 and imaginary coordinates 3 and 4; both inverse laws are proved.",
                DescribeRole.Definition),
            Claim("tangent_finrank", "The tangent dimension",
                Seq(Call(Qualified("Module", "finrank"), RealType, Name("tangent")), Eq, D(4)),
                "The real linear equivalence gives dimension four."),
            Claim("gradient_restricted", "Restriction to the nonzero Wigner points",
                Seq(Name("gradient"), Eq,
                    new Formula.Subscript(Sum, Member(QP,
                        Parenthesized(Seq(Qualified("Finset", "univ"), Setminus, Name("zeroPoints"))))),
                    SignedPhase(Projection(QP, 1), Projection(QP, 2))),
                "The terms omitted from the full gradient sum have zero SignType coefficient."),
            Paragraph(Text("Names below are the public Lean names in "
                + "D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry. "
                + "zeta is the fifth root of unity used in psi and phasePoint. "
                + "wigner is the real phase-point quadratic form divided by five; "
                + "lOne sums the absolute values of its twenty-five entries.")),
            Paragraph(Text("zeroPoints is the set of vanishing Wigner entries of psi. "
                + "tangent imposes complex orthogonality to psi and vanishing real "
                + "phase-point pairings at every point of zeroPoints.")),
            Describe.Lean(DescribeId.Create("ququint-critical-geometry"),
                DeclarationHandle.Create(Module + "critical_geometry"),
                H("Exact zero set and dimension"),
                StatementSource.FromAuthor(Disp(Seq(
                    Name("zeroPoints"), Eq, OpenBrace,
                    Parenthesized(Seq( D(0), Comma, D(3))), Comma,
                    Parenthesized(Seq( D(1), Comma, D(3))), Comma,
                    Parenthesized(Seq( D(2), Comma, D(4))), Comma,
                    Parenthesized(Seq( D(3), Comma, D(1))), Comma,
                    Parenthesized(Seq( D(4), Comma, D(4))), CloseBrace,
                    Sp, Land, Sp, Name("Finset"), Dot, Name("card"), Parenthesized(Seq(
                    Name("zeroPoints"))), Eq, D(5),
                    Sp, Land, Sp, Name("Module"), Dot, Name("finrank"), Parenthesized(Seq(
                    Mathbb, Grp(F.Id("R")), Comma, Name("tangent"))), Eq, D(4),
                    Sp, Land, Sp, Name("lOne"), Parenthesized(Seq( Name("psi"))), Eq, D(1), Plus,
                    D(2), Sqrt, Grp(D(5)), Slash, D(5)))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/erewgoldstein2025magic")),
                Blocks(Paragraph(Text("The exact Wigner table is evaluated using radical. "
                    + "The public real linear equivalence tangentEquiv gives four "
                    + "real coordinates on tangent. Its inverse removes the component "
                    + "phases and selects four real coordinates. Checked matrix "
                    + "identities establish both inverse laws for the original "
                    + "constraint subspace."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ququint-critical-gradient"),
                DeclarationHandle.Create(Module + "gradient_psi"),
                H("Critical gradient"),
                StatementSource.FromAuthor(Disp(Seq(Name("Matrix"), Dot, Name("mulVec"),
                    Parenthesized(Seq( Name("gradient"), Comma, Name("WithLp"), Dot, Name("ofLp"),
                    Parenthesized(Seq( Name("psi"))))), Eq,
                    Parenthesized(Seq( D(5), Cdot, Name("lOne"), Parenthesized(Seq( Name("psi"))),
                    Colon, Mathbb, Grp(F.Id("C")))), Cdot,
                    Name("WithLp"), Dot, Name("ofLp"), Parenthesized(Seq( Name("psi")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/erewgoldstein2025magic")),
                Blocks(Paragraph(Text("gradient is the sum of phasePoint matrices weighted "
                    + "by SignType.sign of the Wigner entries of psi. The public gradient_restricted identity "
                    + "identifies this restricted sum with gradient, whose definition "
                    + "includes all points and has zero coefficients on zeroPoints."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ququint-first-variation-zero"),
                DeclarationHandle.Create(Module + "first_variation_zero"),
                H("Vanishing first variation"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("v"), Colon, Name("tangent"), Comma,
                    Name("HasDerivAt"), Parenthesized(Seq( Parenthesized(Seq( Parenthesized(Seq( F.Id("e"), Colon,
                    Mathbb, Grp(F.Id("R")))), Mapsto, Sp,
                    Name("lOne"), Parenthesized(Seq( Name("psi"), Plus, F.Id("e"), Cdot,
                    Parenthesized(Seq( F.Id("v"), Colon, Name("State"))))))), Comma, D(0), Comma, D(0)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/erewgoldstein2025magic")),
                Blocks(Paragraph(Text("The Lean statement is HasDerivAt with derivative "
                    + "zero, for every vector in tangent. Hermitian symmetry gives an exact "
                    + "quadratic expansion of each Wigner entry. On zeroPoints the linear "
                    + "coefficient vanishes. At the other points the derivative of "
                    + "absolute value multiplies the coefficient by its sign, and "
                    + "the gradient identity and orthogonality to psi make their sum zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ququint-wigner-expand"),
                DeclarationHandle.Create(Module + "wigner_expand"), H("Exact Wigner expansion"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), Colon, Name("State"), Comma,
                    Forall, Sp, F.Id("q"), Sp, F.Id("p"), Colon, Name("Fin"), Sp, D(5), Comma,
                    Forall, Sp, F.Id("e"), Colon, Mathbb, Grp(F.Id("R")), Comma,
                    Call(Name("wigner"), Seq(Name("psi"), Plus, F.Id("e"), Cdot, Sp, F.Id("v")),
                        F.Id("q"), F.Id("p")), Eq,
                    Call(Name("wigner"), Name("psi"), F.Id("q"), F.Id("p")), Plus,
                    F.Id("e"), Cdot, Coefficient(F.Id("v")), Plus,
                    F.Id("e"), Caret, Grp(D(2)), Cdot,
                    Call(Name("wigner"), F.Id("v"), F.Id("q"), F.Id("p"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This existing expansion is now public for normalized perturbations. "
                    + "The proof uses the Hermitian phase-point pairings and real scalar multiplication."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ququint-first-coefficient-zero"),
                DeclarationHandle.Create(Module + "first_coefficient_zero"), H("Cancellation of the linear sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), Colon, Name("tangent"), Comma,
                    Sum, Underscore, Grp(Seq(F.Id("q"), Colon, Name("Fin"), Sp, D(5))),
                    Sum, Underscore, Grp(Seq(F.Id("p"), Colon, Name("Fin"), Sp, D(5))),
                    Parenthesized(Seq( Call(Seq(Name("SignType"), Dot, Name("sign")),
                        Call(Name("wigner"), Name("psi"), F.Id("q"), F.Id("p"))),
                    Colon, Mathbb, Grp(F.Id("R")))), Cdot,
                    Coefficient(Seq(Parenthesized(Seq( F.Id("v"), Colon, Name("State"))))), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("gradient_psi, Hermitian symmetry, and the complex orthogonality "
                    + "in tangent prove this exact cancellation. QuquintStrictDecrease uses this equality "
                    + "when summing its locally valid absolute-value expansions."))),
                DescribeRole.Theorem),
            Paragraph(Text("Scope: this module concerns this state in dimension five. "
                + "It does not claim a general solution of mana extremisation, results "
                + "in other dimensions or at other critical points, that Claim C is "
                + "the authors' verbatim conjecture, or global novelty beyond the "
                + "recorded search. The normalized direction result is developed in QuquintStrictDecrease.")))));

    private static DocumentBlock Claim(string name, string title, Formula statement, string explanation,
        DescribeRole role = DescribeRole.Theorem, bool literature = false) => Describe.Lean(
        DescribeId.Create("ququint-geometry-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Module + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        literature ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/erewgoldstein2025magic"))
            : AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);

    private static Formula BasisRows => Vector(
        Vector(Seq(Minus, D(1)), Seq(R2, Slash, D(4), Minus, D(3)), Seq(Minus, R3, Slash, D(1, 0), Plus, R), Seq(Minus, R3, Slash, D(4, 0))),
        Vector(Seq(D(3), Minus, R2, Slash, D(4)), Seq(D(3), Minus, R2, Slash, D(4)),
            Seq(D(3), Cdot, R3, Slash, D(4, 0), Minus, R), Seq(Minus, D(3), Cdot, R3, Slash, D(4, 0), Plus, R)),
        Vector(Seq(R2, Slash, D(4), Minus, D(3)), Seq(Minus, D(1)), Seq(R3, Slash, D(4, 0)), Seq(R3, Slash, D(1, 0), Minus, R)),
        Vector(D(1), D(0), D(0), D(0)), Vector(D(0), D(1), D(0), D(0)),
        Vector(D(0), D(0), Seq(Minus, D(1)), Seq(D(2), Minus, R2, Slash, D(4))),
        Vector(D(0), D(0), Seq(R2, Slash, D(4), Minus, D(2)), Seq(R2, Slash, D(4), Minus, D(2))),
        Vector(D(0), D(0), Seq(D(2), Minus, R2, Slash, D(4)), Seq(Minus, D(1))),
        Vector(D(0), D(0), D(1), D(0)), Vector(D(0), D(0), D(0), D(1)));
    private static Formula Ungauged(string part, int index) => Call(Qualified("Complex", part),
        Seq(Call(OfLp(Cast(V, Name("State"))), Num(index)), Slash, Call(Name("phases"), Num(index))));
    private static Formula R => Name("radical");
    private static Formula R2 => Power(R, D(2));
    private static Formula R3 => Power(R, D(3));
    private static Formula PhaseVector => Vector(D(1), D(1), Power(Name("zeta"), D(3)), D(1), Power(Name("zeta"), D(2)));
    private static Formula ZeroSet => new Formula.SetLiteral([Point(0, 3), Point(1, 3), Point(2, 4), Point(3, 1), Point(4, 4)]);
    private static Formula Point(int q, int p) => Parenthesized(Seq(Num(q), Comma, Num(p)));
    private static Formula SignedPhase(Formula q, Formula p) => Seq(
        Cast(Call(Qualified("SignType", "sign"), Call(Name("wigner"), Name("psi"), q, p)), ComplexType),
        Cdot, Call(Name("phasePoint"), q, p));
    private static Formula Pair(Formula u, Formula v) => Call(Name("dotProduct"), Call(Name("star"), u), v);
    private static Formula MulVec(Formula m, Formula v) => Call(Qualified("Matrix", "mulVec"), m, v);
    private static Formula OfLp(Formula v) => Call(Qualified("WithLp", "ofLp"), v);
    private static Formula Projection(Formula v, int i) => Seq(Parenthesized(v), Dot, Num(i));
    private static Formula Cast(Formula v, Formula type) => Parenthesized(Seq(v, Colon, type));
    private static Formula ModFive(Formula v) => Cast(v, Call(Name("ZMod"), D(5)));
    private static Formula Power(Formula v, Formula exponent) => new Formula.Power(v, exponent);
    private static Formula Member(Formula v, Formula set) => new Formula.Relation(v, FormulaRelationOperator.MemberOf, set);
    private static Formula SumOver(Formula v, Formula type) => new Formula.Subscript(Sum, Seq(v, Colon, type));
    private static Formula Vector(params Formula[] entries) => Seq(OpenBracket,
        Seq(entries.SelectMany((v, i) => i == 0 ? new[] { v } : new[] { Comma, v }).ToArray()), CloseBracket);
    private static Formula MatrixType(int rows, int cols, Formula field) => Call(Name("Matrix"), Fin(rows), Fin(cols), field);
    private static Formula RealCoordinates(int n) => Parenthesized(Seq(Fin(n), To, RealType));
    private static Formula PointType => Parenthesized(Seq(Fin(5), Times, Fin(5)));
    private static Formula Fin(int n) => Seq(Name("Fin"), Sp, Num(n));
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Qualified(string module, string name) => Seq(Name(module), Dot, Name(name));
    private static Formula Q => F.Id("q");
    private static Formula P => F.Id("p");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula V => F.Id("v");
    private static Formula U => F.Id("u");
    private static Formula I => F.Id("i");
    private static Formula A => F.Id("a");
    private static Formula QP => F.Id("qp");

    private static Formula Coefficient(Formula v) => Seq(Parenthesized(Seq( D(2), Cdot,
        Call(Seq(Name("Complex"), Dot, Name("re")),
            Call(Name("dotProduct"), Call(Name("star"), Call(Seq(Name("WithLp"), Dot, Name("ofLp")), Name("psi"))),
                Call(Seq(Name("Matrix"), Dot, Name("mulVec")),
                    Call(Name("phasePoint"), F.Id("q"), F.Id("p")),
                    Call(Seq(Name("WithLp"), Dot, Name("ofLp")), v)))), Slash, D(5))));
    private static Formula Call(Formula f, params Formula[] args) => Seq(f, Parenthesized(
        Seq(args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, arg }).ToArray())));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
