using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class APNBreakingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/APNBreakingRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An almost perfect nonlinear map on a field with sixteen elements sends a "
            + "three-dimensional binary flat onto another three-dimensional binary flat.",
        H("APN Maps Need Not Break Large Flats"),
        Blocks(
            Node("apn", "Almost perfect nonlinearity", "APN", APNFormula(),
                "For each nonzero additive direction a and each value b, the equation "
                    + "F(x+a)+F(x)=b has at most two solutions. The definition applies to "
                    + "finite additive commutative groups and agrees with the APN condition "
                    + "on fields of characteristic two.", DescribeRole.Definition),
            Node("affine-flat", "Binary affine flats", "affineFlat", AffineFlatFormula(),
                "For a binary subspace V, membership of x in the coset a+V means x-a "
                    + "belongs to V. The dimension of the coset is the dimension of V.",
                DescribeRole.Definition),
            Node("is-flat", "Being an affine flat", "IsFlat", IsFlatFormula(),
                "An image is a flat when it is some coset of some binary subspace. "
                    + "The subspace may have any dimension; no injectivity assumption "
                    + "is imposed on the map.", DescribeRole.Definition),
            Node("breaking-claim", "Conjecture 3.1", "claim", ClaimFormula(),
                "Rodriguez-Aldama, Sehovic, Pasalic and Kudin, arXiv:2609.22394v2, "
                    + "Conjecture 3.1, assert that every APN function over a field of order "
                    + "2 to the n breaks every k-flat for floor(n/2)+1 <= k <= n-1. "
                    + "Here the field, the function, the integer k, the coset offset and "
                    + "the subspace all remain arbitrary. The binary module structure "
                    + "comes from the prime-field algebra of the characteristic-two field.",
                DescribeRole.Definition),
            Node("apn-coordinates", "APN invariance under additive coordinates",
                "apn_conjugate_iff", APNTransportFormula(),
                "An additive isomorphism e takes each derivative fiber bijectively to "
                    + "the derivative fiber in direction e(a) with value e(b). Thus "
                    + "conjugating a function by e preserves the APN condition in both "
                    + "directions.", DescribeRole.Theorem),
            Node("flat-coordinates", "Cosets and dimensions under linear coordinates",
                "affineFlat_image", FlatTransportFormula(),
                "A binary linear isomorphism takes a+V to e(a)+e(V), and the "
                    + "restriction to V preserves its dimension. This supplies the "
                    + "coordinate-independent interpretation of both flats.", DescribeRole.Theorem),
            Node("binary-coordinates", "Four binary coordinates", "W",
                Disp(Equal(F.Id("W"), new Formula.TypeArrow(Call("Fin", D(4)), BinaryField()))),
                "Coordinates are ordered from the least significant bit to the most "
                    + "significant bit. The vector (a,b,c,d) has label a+2b+4c+8d.",
                DescribeRole.Definition),
            Node("table-map", "The sixteen-value function", "G", TableFormula(),
                "The listed values, read in label order from zero through fifteen, "
                    + "define G. The table originates from x cubed plus a binary linear "
                    + "map L in the polynomial field model with modulus x to the fourth "
                    + "plus x plus one, where L has column labels 8,12,12,5. The argument "
                    + "uses the table itself and asserts no polynomial identity for G.",
                DescribeRole.Definition),
            Node("refutation", "Failure at n = 4 and k = 3", "result",
                Disp(new Formula.Not(F.Id("claim"))),
                "The input subspace has labels {0,1,2,3,8,9,10,11}, equivalently its "
                    + "third bit is zero. Its eight elements make its binary dimension "
                    + "three. Their images have labels {0,2,4,6,9,11,13,15}, the subspace "
                    + "whose first and fourth bits agree, spanned by labels 2,4,9. "
                    + "Every nonzero derivative fiber of G has at most two elements. "
                    + "The four-dimensional binary vector space is linearly isomorphic "
                    + "to GaloisField(2,4). Conjugate G and transport the two subspaces "
                    + "along this isomorphism. The field has sixteen elements, and k=3 "
                    + "satisfies both bounds. Its APN map therefore has an affine-flat "
                    + "image on a permitted flat, contradicting the conjecture. Field "
                    + "multiplication is never needed for this counterexample.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rodriguez-aldama-et-al-2026-apn-breaking-refutation"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Nat() => F.Id("Nat");
    private static Formula BinaryField() => Call("ZMod", D(2));
    private static Formula Spaces(Formula m) => Call("Submodule", BinaryField(), m);
    private static Formula Compose(Formula a, Formula b) => Seq(a, Sp, Circ, Sp, b);

    private static Formula APNFormula()
    {
        var m = F.Id("M"); var f = F.Id("F"); var a = F.Id("a");
        var b = F.Id("b"); var x = F.Id("x");
        var fiber = Seq(OpenBrace, Sp, x, Sp, InMacro, Sp, m, Sp, Bar, Sp,
            Equal(Add(Call("F", Add(x, a)), Call("F", x)), b), Sp, CloseBrace);
        return Disp(All("F", new Formula.TypeArrow(m, m),
            Iff(Call("APN", f), All("a", m, All("b", m,
                Imp(new Formula.Not(Equal(a, D(0))), Le(Call("card", fiber), D(2))))))));
    }

    private static Formula AffineFlatFormula()
    {
        var m = F.Id("M"); var a = F.Id("a"); var v = F.Id("V"); var x = F.Id("x");
        return Disp(All("a", m, All("V", Spaces(m), Equal(Call("affineFlat", a, v),
            Seq(OpenBrace, Sp, x, Sp, InMacro, Sp, m, Sp, Bar, Sp,
                Call("mem", Sub(x, a), v), Sp, CloseBrace)))));
    }

    private static Formula IsFlatFormula()
    {
        var m = F.Id("M"); var a = F.Id("a"); var v = F.Id("V"); var s = F.Id("A");
        return Disp(All("A", Call("Set", m), Iff(Call("IsFlat", s),
            Some("a", m, Some("V", Spaces(m), Equal(s, Call("affineFlat", a, v)))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var field = F.Id("K");
        var f = F.Id("F"); var a = F.Id("a"); var v = F.Id("V");
        var fieldConditions = And(Call("Field", field), And(Call("Fintype", field),
            And(Call("DecidableEq", field), Call("CharP", field, D(2)))));
        var range = And(Le(Add(Seq(Lfloor, Sp, new Formula.Fraction(n, D(2)), Sp, Rfloor),
            D(1)), k), Le(k, Sub(n, D(1))));
        var conclusion = new Formula.Not(Call("IsFlat", Call("image", f,
            Call("affineFlat", a, v))));
        var body = All("a", field, All("V", Spaces(field),
            Imp(Equal(Call("finrank", BinaryField(), v), k), conclusion)));
        body = All("k", Nat(), Imp(range, body));
        body = All("F", new Formula.TypeArrow(field, field), Imp(Call("APN", f), body));
        body = All("n", Nat(), Imp(Equal(Call("card", field), new Formula.Power(D(2), n)), body));
        body = All("K", F.Id("Type"), Imp(fieldConditions, body));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula APNTransportFormula()
    {
        var m = F.Id("M"); var n = F.Id("N"); var e = F.Id("e"); var f = F.Id("F");
        return Disp(All("e", Call("AddEquiv", m, n),
            All("F", new Formula.TypeArrow(m, m), Iff(Call("APN",
                Compose(Compose(e, f), Call("inverse", e))), Call("APN", f)))));
    }

    private static Formula FlatTransportFormula()
    {
        var m = F.Id("M"); var n = F.Id("N"); var e = F.Id("e");
        var a = F.Id("a"); var v = F.Id("V"); var mapped = Call("map", v, e);
        return Disp(All("e", Call("LinearEquiv", BinaryField(), m, n), All("a", m,
            All("V", Spaces(m), And(Equal(Call("image", e, Call("affineFlat", a, v)),
                Call("affineFlat", Call("e", a), mapped)),
                Equal(Call("finrank", BinaryField(), mapped),
                    Call("finrank", BinaryField(), v)))))));
    }

    private static Formula TableFormula() => Disp(Seq(
        Call("labelValues", F.Id("G")), Sp, Eq, Sp, OpenBracket,
        D(0), Comma, Sp, D(9), Comma, Sp, D(4), Comma, Sp, D(1,1), Comma, Sp,
        D(0), Comma, Sp, D(1,4), Comma, Sp, D(1), Comma, Sp, D(9), Comma, Sp,
        D(1,5), Comma, Sp, D(2), Comma, Sp, D(6), Comma, Sp, D(1,3), Comma, Sp,
        D(1), Comma, Sp, D(1,1), Comma, Sp, D(1,3), Comma, Sp, D(1), CloseBracket));
}
