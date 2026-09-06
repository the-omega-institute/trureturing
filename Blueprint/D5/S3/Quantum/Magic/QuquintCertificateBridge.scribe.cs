using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintCertificateBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Magic/QuquintCertificateBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The numerical certificate data are the actual ququint tangent forms.",
        H("Ququint Certificate Geometry Bridge"),
        Blocks(
            Claim("complexBasis", "The complex tangent basis",
                Seq(Forall, Sp, I, Colon, Fin(5), Comma, Forall, Sp, J, Colon, Fin(4), Comma,
                    Call(Name("complexBasis"), I, J), Eq, Call(Geo("phases"), I), Cdot,
                    Call(Local("Complex", "mk"),
                        Call(Geo("basisMatrix"), Call(Local("Fin", "castAdd"), D(5), I), J),
                        Call(Geo("basisMatrix"), Call(Local("Fin", "natAdd"), D(5), I), J))),
                "complexBasis has type Matrix (Fin 5) (Fin 4) C. The two real halves of basisMatrix "
                    + "become the real and imaginary components before phase multiplication.", DescribeRole.Definition),
            Claim("pullback", "The real pullback matrix",
                Seq(Forall, Sp, M, Colon, MatrixType(5, 5, ComplexType), Comma,
                    Forall, Sp, I, Sp, J, Colon, Fin(4), Comma,
                    Call(Name("pullback"), M, I, J), Eq,
                    Call(Local("Complex", "re"), Call(Name("dotProduct"),
                        Call(Name("star"), Lambda(K, Fin(5), Call(Name("complexBasis"), K, I))),
                        Call(Local("Matrix", "mulVec"), M, Lambda(K, Fin(5), Call(Name("complexBasis"), K, J))))),
                    Slash, D(5)),
                "The pullback has type Matrix (Fin 4) (Fin 4) R. This expression defines each entry.",
                DescribeRole.Definition),
            Claim("phaseForm", "The pulled-back phase-point form",
                Seq(Forall, Sp, Q, Sp, P, Colon, Fin(5), Comma,
                    Call(Name("phaseForm"), Q, P), Eq, Call(Name("pullback"), Call(Geo("phasePoint"), Q, P))),
                "Each phaseForm is a four-by-four real matrix obtained by the displayed pullback definition.",
                DescribeRole.Definition),
            Claim("gram", "The coordinate Gram matrix",
                Seq(Name("gram"), Colon, MatrixType(4, 4, RealType), Eq,
                    Call(Local("Matrix", "transpose"), Geo("basisMatrix")), Cdot, Geo("basisMatrix")),
                "gram is the explicit numerical table in Lean. The public identity gram_eq below proves "
                    + "that its defining geometric expression is this real matrix product.", DescribeRole.Definition),
            Claim("signs", "The complete Wigner sign table",
                Seq(Name("signs"), Colon, MatrixType(5, 5, Name("SignType")), Eq,
                    Vector(Vector(Seq(Minus, D(1)), D(1), D(1), D(0), D(1)), Vector(Seq(Minus, D(1)), D(1), D(1), D(0), D(1)),
                        Vector(D(1), Seq(Minus, D(1)), D(1), D(1), D(0)), Vector(D(1), D(0), D(1), Seq(Minus, D(1)), D(1)),
                        Vector(D(1), Seq(Minus, D(1)), D(1), D(1), D(0)))),
                "Rows are indexed by q and columns by p. signs_eq proves agreement with SignType.sign.",
                DescribeRole.Definition),
            Claim("zeroIndex", "The ordered zero-point enumeration",
                Seq(Name("zeroIndex"), Colon, Fin(5), To, Parenthesized(Seq(Fin(5), Times, Fin(5))), Eq,
                    Vector(Point(0, 3), Point(1, 3), Point(2, 4), Point(3, 1), Point(4, 4))),
                "The order is the same as the five entries of QuquintCertificateData.zeroQ.", DescribeRole.Definition),
            Claim("realification", "The real and imaginary blocks",
                Seq(Forall, Sp, M, Colon, MatrixType(5, 5, ComplexType), Comma,
                    Forall, Sp, I, Sp, J, Colon, Fin(10), Comma,
                    Call(Name("realification"), M, I, J), Eq,
                    Call(Local("Fin", "addCases"),
                        Lambda(X, Fin(5), Call(Local("Fin", "addCases"),
                            Lambda(Y, Fin(5), EntryPart("re")), Lambda(Y, Fin(5), Seq(Minus, EntryPart("im"))), J)),
                        Lambda(X, Fin(5), Call(Local("Fin", "addCases"),
                            Lambda(Y, Fin(5), EntryPart("im")), Lambda(Y, Fin(5), EntryPart("re")), J)), I)),
                "The resulting Matrix (Fin 10) (Fin 10) R has blocks [Re, -Im; Im, Re]. "
                    + "Fin.addCases fixes the real-first, imaginary-second order on each axis.", DescribeRole.Definition),
            Claim("zeroQ_0_eq", "Zero form at the first point",
                Seq(Call(Data("zeroQ"), D(0)), Eq, Call(Name("phaseForm"), D(0), D(3))),
                "Exact entrywise arithmetic verifies the first numerical zero form."),
            Claim("zeroQ_1_eq", "Zero form at the second point",
                Seq(Call(Data("zeroQ"), D(1)), Eq, Call(Name("phaseForm"), D(1), D(3))),
                "Exact entrywise arithmetic verifies the second numerical zero form."),
            Claim("zeroQ_2_eq", "Zero form at the third point",
                Seq(Call(Data("zeroQ"), D(2)), Eq, Call(Name("phaseForm"), D(2), D(4))),
                "Exact entrywise arithmetic verifies the third numerical zero form."),
            Claim("zeroQ_3_eq", "Zero form at the fourth point",
                Seq(Call(Data("zeroQ"), D(3)), Eq, Call(Name("phaseForm"), D(3), D(1))),
                "Exact entrywise arithmetic verifies the fourth numerical zero form."),
            Claim("zeroQ_4_eq", "Zero form at the fifth point",
                Seq(Call(Data("zeroQ"), D(4)), Eq, Call(Name("phaseForm"), D(4), D(4))),
                "Exact entrywise arithmetic verifies the fifth numerical zero form."),
            Paragraph(Text("complexBasis applies the component phases to the real and imaginary "
                + "halves of basisMatrix. pullback is the real part of the resulting complex "
                + "matrix contraction divided by five; phaseForm applies it to phasePoint. "
                + "realification uses the real blocks Re, -Im, Im, Re in that order. "
                + "All imported declarations in the formulas retain their full Lean namespaces.")),
            Claim("complexBasis_tangentEquiv", "The same tangent coordinates",
                Seq(Forall, Sp, F.Id("a"), Colon, Coordinates, Comma,
                    Name("Matrix"), Dot, Name("mulVec"), Parenthesized(Seq( Name("complexBasis"), Comma,
                    Parenthesized(Seq( Parenthesized(Seq( F.Id("i"), Colon, Name("Fin"), Sp, D(4))), Mapsto,
                    Parenthesized(Seq( F.Id("a"), Parenthesized(Seq( F.Id("i"))), Colon, Mathbb, Grp(F.Id("C")))))))), Eq, Name("WithLp"), Dot, Name("ofLp"), Parenthesized(Seq(
                    Parenthesized(Seq( Geo("tangentEquiv"), Parenthesized(Seq( F.Id("a"))), Colon, Geo("State")))))),
                "The columns give exactly the public real linear equivalence onto tangent."),
            Claim("phaseForm_realification", "Literal phase-point realification",
                Seq(Forall, Sp, F.Id("q"), Sp, F.Id("p"), Colon, Name("Fin"), Sp, D(5), Comma,
                    Name("phaseForm"), Parenthesized(Seq( F.Id("q"), Comma, F.Id("p"))), Eq,
                    D(1), Slash, D(5), Cdot, Name("Matrix"), Dot, Name("transpose"),
                    Parenthesized(Seq( Geo("basisMatrix"))), Cdot, Name("realification"), Parenthesized(Seq(
                    Name("Matrix"), Dot, Name("conjTranspose"), Parenthesized(Seq(
                    Name("Matrix"), Dot, Name("diagonal"), Parenthesized(Seq( Geo("phases"))))),
                    Cdot, Geo("phasePoint"), Parenthesized(Seq( F.Id("q"), Comma, F.Id("p"))),
                    Cdot, Name("Matrix"), Dot, Name("diagonal"), Parenthesized(Seq( Geo("phases"))))), Cdot, Geo("basisMatrix")),
                "Diagonal conjugation and the realification blocks give the stated identity for every phase point."),
            Claim("gram_eq", "The numerical Gram matrix",
                Seq(Name("gram"), Eq, Name("Matrix"), Dot, Name("transpose"),
                    Parenthesized(Seq( Geo("basisMatrix"))), Cdot, Geo("basisMatrix")),
                "Every entry of the explicit numerical gram matrix is checked against this product."),
            Claim("signs_eq", "The numerical sign table",
                Seq(Forall, Sp, F.Id("q"), Sp, F.Id("p"), Colon, Name("Fin"), Sp, D(5), Comma,
                    Name("signs"), Parenthesized(Seq( F.Id("q"), Comma, F.Id("p"))), Eq,
                    Name("SignType"), Dot, Name("sign"), Parenthesized(Seq( Geo("wigner"), Parenthesized(Seq(
                    Geo("psi"), Comma, F.Id("q"), Comma, F.Id("p")))))),
                "The literal twenty-five-entry sign table agrees with the signs of the Wigner values, including all zeros."),
            Claim("zeroIndex_image", "Exactly the vanishing points",
                Seq(Name("Finset"), Dot, Name("image"), Parenthesized(Seq( Name("zeroIndex"), Comma,
                    Name("Finset"), Dot, Name("univ"))), Eq, Geo("zeroPoints")),
                "zeroIndex enumerates (0,3), (1,3), (2,4), (3,1), (4,4) in the order of the numerical data."),
            Claim("zeroQ_eq", "All five numerical zero forms",
                Seq(Forall, Sp, F.Id("i"), Colon, Name("Fin"), Sp, D(5), Comma,
                    Data("zeroQ"), Parenthesized(Seq( F.Id("i"))), Eq,
                    Name("phaseForm"), Parenthesized(Seq( Parenthesized(Seq( Name("zeroIndex"), Parenthesized(Seq( F.Id("i"))))), Dot, D(1), Comma, Parenthesized(Seq( Name("zeroIndex"), Parenthesized(Seq( F.Id("i"))))), Dot, D(2)))),
                "The five named entrywise computations zeroQ_0_eq through zeroQ_4_eq establish this enumeration identity."),
            Claim("base_eq_gradient", "The numerical base matrix",
                Seq(Data("base"), Eq, Name("pullback"), Parenthesized(Seq( Geo("gradient"))),
                    Minus, Geo("lOne"), Parenthesized(Seq( Geo("psi"))), Cdot, Name("gram")),
                "Exact quartic-field arithmetic identifies all sixteen entries, including the subtracted norm term."),
            Claim("base_eq", "The actual nonzero sign contribution",
                Seq(Data("base"), Eq, Parenthesized(Seq(
                    new Formula.Subscript(Sum, new Formula.Relation(F.Id("qp"), FormulaRelationOperator.MemberOf,
                        Parenthesized(Seq(Name("Finset"), Dot, Name("univ"), Setminus, Geo("zeroPoints"))))),
                    Parenthesized(Seq( Name("SignType"), Dot, Name("sign"), Parenthesized(Seq( Geo("wigner"), Parenthesized(Seq(
                    Geo("psi"), Comma, F.Id("qp"), Dot, D(1), Comma, F.Id("qp"), Dot, D(2))))), Colon, Mathbb, Grp(F.Id("R")))), Cdot,
                    Name("phaseForm"), Parenthesized(Seq( F.Id("qp"), Dot, D(1), Comma, F.Id("qp"), Dot, D(2))))),
                    Minus, Geo("lOne"), Parenthesized(Seq( Geo("psi"))), Cdot, Name("gram")),
                "The base is the signed sum over exactly the nonzero points, minus lOne of psi times gram."),
            Claim("phaseForm_eval", "Evaluation through tangentEquiv",
                Seq(Forall, Sp, F.Id("q"), Sp, F.Id("p"), Colon, Name("Fin"), Sp, D(5), Comma,
                    Forall, Sp, F.Id("a"), Colon, Coordinates, Comma,
                    Name("dotProduct"), Parenthesized(Seq( F.Id("a"), Comma, Name("Matrix"), Dot, Name("mulVec"),
                    Parenthesized(Seq( Name("phaseForm"), Parenthesized(Seq( F.Id("q"), Comma, F.Id("p"))),
                    Comma, F.Id("a"))))), Eq,
                    Geo("wigner"), Parenthesized(Seq( Parenthesized(Seq( Geo("tangentEquiv"), Parenthesized(Seq( F.Id("a"))),
                    Colon, Geo("State"))), Comma, F.Id("q"), Comma, F.Id("p")))),
                "Contracting the real matrix computes the Wigner quadratic form of the actual tangent vector."),
            Claim("gram_eval", "Evaluation of the squared norm",
                Seq(Forall, Sp, F.Id("a"), Colon, Coordinates, Comma,
                    Name("dotProduct"), Parenthesized(Seq( F.Id("a"), Comma, Name("Matrix"), Dot, Name("mulVec"),
                    Parenthesized(Seq( Name("gram"), Comma, F.Id("a"))))), Eq,
                    Name("Norm"), Dot, Name("norm"), Parenthesized(Seq( Parenthesized(Seq( Geo("tangentEquiv"), Parenthesized(Seq( F.Id("a"))),
                    Colon, Geo("State"))))), Caret, Grp(D(2))),
                "Each component phase has norm one, so the real Gram contraction is the squared norm in State."),
            Paragraph(Text("This module proves only the identification of the certificate data with "
                + "the ququint geometry. QuquintFiniteMaximum uses the bridge for the finite sign "
                + "maximum and negativity equivalence. The normalized perturbation identity "
                + "and strict mana decrease are proved in QuquintStrictDecrease.exact_change "
                + "and QuquintStrictDecrease.directional_decrease for the constrained tangent family. "
                + "It makes no claim about general mana extremisation, other dimensions or critical "
                + "points, author-verbatim Claim C, or global novelty.")))));

    private static DocumentBlock Claim(string name, string title, Formula statement, string explanation,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("ququint-bridge-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula Lambda(Formula v, Formula type, Formula body) =>
        Parenthesized(Seq(Parenthesized(Seq(v, Colon, type)), Mapsto, body));
    private static Formula EntryPart(string part) => Call(Local("Complex", part), Call(M, X, Y));
    private static Formula MatrixType(int rows, int cols, Formula field) => Call(Name("Matrix"), Fin(rows), Fin(cols), field);
    private static Formula Vector(params Formula[] entries) => Seq(OpenBracket,
        Seq(entries.SelectMany((v, i) => i == 0 ? new[] { v } : new[] { Comma, v }).ToArray()), CloseBracket);
    private static Formula Point(int q, int p) => Parenthesized(Seq(Num(q), Comma, Num(p)));
    private static Formula Fin(int n) => Seq(Name("Fin"), Sp, Num(n));
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Local(string module, string name) => Seq(Name(module), Dot, Name(name));
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula K => F.Id("k");
    private static Formula Q => F.Id("q");
    private static Formula P => F.Id("p");
    private static Formula M => F.Id("m");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula Call(Formula f, params Formula[] args) => Seq(f, Parenthesized(
        Seq(args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, arg }).ToArray())));

    private static Formula Coordinates => Seq(Parenthesized(Seq( Name("Fin"), Sp, D(4), To,
        Mathbb, Grp(F.Id("R")))));
    private static Formula Geo(string name) => Qualified("QuquintWignerCriticalGeometry", name);
    private static Formula Data(string name) => Qualified("QuquintCertificateData", name);
    private static Formula Qualified(string module, string name) => Seq(Name("D5"), Dot,
        Name("S3"), Dot, Name("Quantum"), Dot, Name("Magic"), Dot, Name(module), Dot, Name(name));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
