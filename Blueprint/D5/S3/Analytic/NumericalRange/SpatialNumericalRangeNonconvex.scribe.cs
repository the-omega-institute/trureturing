using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.NumericalRange;

internal sealed class SpatialNumericalRangeNonconvexDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/dedaniapatel2024spatial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-dimensional complex normed algebra has two spatial numerical range points whose midpoint is absent.",
        H("Dedania–Patel Spatial Numerical Range Convexity Refutation"),
        Blocks(
            SourceQuotation(),
            Entry("spatial-range", "spatialNumericalRange", "Spatial numerical range", SpatialRange(),
                "Formal encoding of the quoted definition: for a complex normed algebra A, spatialNumericalRange a consists of the values φ(a*x), where x is a unit vector and φ is a continuous complex-linear functional with norm one and φ(x)=1. The algebra has NonUnitalNormedRing, NormedSpace ℂ, IsScalarTower ℂ A A and SMulCommClass ℂ A A instances; convexity is over ℝ.",
                DescribeRole.Definition, true),
            Entry("convexity-claim", "claim", "Universal spatial convexity", Claim(),
                "Dedania and Patel ask in Section 1, page 2: “It is still open problem wether V_A(a) is always convex? This problem is discussed in [5].” The formal claim quantifies over every complex normed algebra with the four indicated instances and every element a, and asserts Convex ℝ (spatialNumericalRange a). It assumes neither completeness nor commutativity.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "An absent midpoint", Disp(Seq(Neg, Sp, V("claim"))),
                "Let P=(1/5)[[1,2],[2,4]] and give ℂ⊕ℂ² the product (α,x)(β,y)=(αβ,αPy+βx) and norm max(3|α|,‖x‖∞). The Lean coordinates use u₀=3α and e=(3,0). Idempotence of P gives associativity, and the multiplication is submultiplicative. The two norming pairs with vectors (0,(1,i)) and (0,(i,1)) and coordinate functionals give z₁=1/5+2i/5 and z₂=4/5+2i/5. For any norm-one functional, the sum of coefficient norms is at most one. The norming equation makes the diagonal products real; attaining imaginary height 2/5 forces the cross products to be purely imaginary. At the midpoint 1/2+2i/5 both coefficient norms would be 1/2, contradicting the identity between the products of the diagonal and cross terms. Thus the midpoint is absent and the universal convexity assertion is false.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("dedania-patel-2024-spatial-numerical-range-convexity"),
                ResolutionKind.Refuted) : null);

    private static DocumentBlock SourceQuotation()
    {
        Formula a = V("A"), x = V("x"), element = V("a");
        Formula sphere = Seq(V("S"), Parenthesized(a));
        Formula dual = new Formula.Power(a, Star);
        Formula norming = Seq(new Formula.Subscript(V("D"), a), Parenthesized(x));
        Formula rangeAt = Seq(new Formula.Subscript(V("V"), a),
            Parenthesized(Seq(element, Semi, x)));
        Formula range = Seq(new Formula.Subscript(V("V"), a), Parenthesized(element));
        Formula phiAtX = Seq(Varphi, Parenthesized(x));
        Formula phiAtProduct = Seq(Varphi, Parenthesized(Seq(element, x)));
        return Paragraph(
            Text("Dedania–Patel, arXiv:2306.16172v1, §1, p. 2, definition verbatim: “Let "),
            Math(Equal(sphere, Seq(OpenBrace, x, InMacro, Sp, a, Colon,
                Equal(new Formula.Norm(x), D(1)), CloseBrace))),
            Text(" be the unit sphere in "), Math(a), Text(". Let "), Math(dual),
            Text(" be the Banach space dual of "), Math(a), Text(". Let "),
            Math(Equal(norming, Seq(OpenBrace, Varphi, InMacro, Sp, dual, Colon,
                new Formula.Norm(Varphi), Eq, D(1), Eq, phiAtX, CloseBrace))),
            Text(" for each "), Math(Seq(x, InMacro, Sp, sphere)), Text(". Further, let "),
            Math(Equal(rangeAt, Seq(OpenBrace, phiAtProduct, Colon,
                Varphi, InMacro, Sp, norming, CloseBrace))),
            Text(" for "), Math(Seq(element, InMacro, Sp, a)), Text(" and "),
            Math(Seq(x, InMacro, Sp, sphere)), Text(". Then "),
            Math(Equal(range, Seq(Cup, OpenBrace, rangeAt, Colon,
                x, InMacro, Sp, sphere, CloseBrace))),
            Text(" is the spatial numerical range (SNR)”"));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula AlgebraContext(Formula body) =>
        All("A", Call("Type"), Seq(
            OpenBracket, Call("NonUnitalNormedRing", V("A")), CloseBracket, Sp,
            OpenBracket, Call("NormedSpace", Complex, V("A")), CloseBracket, Sp,
            OpenBracket, Call("IsScalarTower", Complex, V("A"), V("A")), CloseBracket, Sp,
            OpenBracket, Call("SMulCommClass", Complex, V("A"), V("A")), CloseBracket,
            Comma, Sp, body));

    private static Formula SpatialRange()
    {
        Formula x = V("x");
        Formula phi = V("phi");
        Formula product = Seq(V("a"), Star, x);
        Formula norming = And(Equal(Norm(x), D(1)),
            Some("phi", Call("ContinuousLinearMap", Complex, V("A"), Complex),
                And(Equal(Norm(phi), D(1)),
                    And(Equal(Call("phi", x), D(1)), Equal(Call("phi", product), V("z"))))));
        Formula membership = new Formula.Relation(V("z"), FormulaRelationOperator.MemberOf,
            Call("spatialNumericalRange", V("a")));
        return Disp(AlgebraContext(All("a", V("A"), All("z", Complex,
            Iff(membership, Some("x", V("A"), norming))))));
    }

    private static Formula Claim() => Disp(Iff(V("claim"),
        AlgebraContext(All("a", V("A"),
            Call("Convex", Real, Call("spatialNumericalRange", V("a")))))));
}
