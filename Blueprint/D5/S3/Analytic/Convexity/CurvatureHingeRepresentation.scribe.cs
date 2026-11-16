using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class CurvatureHingeRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.";
    private static Formula P => Call("Positive");
    private static Formula Mu => Call("curvature", Id("h"));
    private static Formula V(string x) => Call("f", Id(x));
    private static Formula R(string x) => Call("rightDeriv", Id("f"), Id(x));
    private static Formula Fn => Arrow(Real(), Real());
    private static Formula Convex => Call("ConvexOn", Real(), Call("Ioi", D(0)), Id("f"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every real convex function on the positive ray has a locally finite Stieltjes curvature and a two-sided hinge representation.",
        H("Convex curvature and finite hinge remainders"), Blocks(
            Paragraph(Text("Positive is the subtype of strictly positive real numbers. Subtype coercions are suppressed in the formulas. The derivative is always the actual right derivative. Curvature is the Stieltjes measure of that derivative on Positive. Its total mass, and its mass near zero, may be infinite. No smoothness, atomlessness, absolute continuity or full-support hypothesis is used. The measure in every displayed curvature integral is curvature h.")),
            Node("Positive", Eqn(P, Call("Ioi", D(0))),
                "The open positive ray, equipped with its induced order, Borel structure and topology.", false),
            Node("rightDeriv", All("f", Fn, All("x", Real(),
                Eqn(R("x"), Call("derivWithin", Id("f"), Call("Ioi", Id("x")), Id("x"))))),
                "The one-sided derivative is selected by Mathlib's derivative within the strict right ray.", false),
            Node("curvatureDistribution", WithConvex(All("x", P,
                Eqn(Call("curvatureDistribution", Id("h"), Id("x")), R("x")))),
                "Monotonicity comes from convexity. Right continuity is proved by squeezing the derivative between its value at the base point and nearby secant slopes to a fixed positive point. This is the actual derivative, rather than an assumed or unverified regularization.", false),
            Node("curvature", WithConvex(Eqn(Mu,
                Call("StieltjesFunction.measure", Call("curvatureDistribution", Id("h"))))),
                "Mathlib constructs a positive Borel Stieltjes measure. The instance curvature_locallyFinite certifies local finiteness on Positive; it makes no claim of finite total curvature.", false),
            Node("curvature_Ioc", WithConvex(All("a", P, All("b", P,
                Eqn(At(Mu, Call("Ioc", Id("a"), Id("b"))),
                    Call("ENNReal.ofReal", Sub(R("b"), R("a"))))))),
                "For a below b, the mass of (a,b] is exactly the increment of the right derivative. The formula is also valid for reversed endpoints, where both sides vanish.", true),
            Node("scalar_remainder_right", WithConvex(All("a", P, All("b", P,
                Imp(Leqn(Id("a"), Id("b")), Eqn(V("b"), Add(Add(V("a"),
                    Mul(R("a"), Sub(Id("b"), Id("a")))),
                    Integral(Call("Ioc", Id("a"), Id("b")), Sub(Id("b"), Id("t"))))))))),
                "On a compact positive interval, the right-derivative fundamental theorem of calculus gives f(b)-f(a). Fubini applied to the bounded indicator t <= x identifies the integral of the derivative increment with the curvature potential. The only curvature involved is the finite measure restricted to (a,b].", true),
            Node("scalar_remainder_left", WithConvex(All("a", P, All("b", P,
                Imp(Leqn(Id("a"), Id("b")), Eqn(V("a"), Add(Add(V("b"),
                    Mul(R("b"), Sub(Id("a"), Id("b")))),
                    Integral(Call("Ioc", Id("a"), Id("b")), Sub(Id("t"), Id("a"))))))))),
                "The left remainder uses the right derivative at the upper endpoint. Subtracting the complementary triangle potential from the constant interval potential includes the full atom at that endpoint.", true),
            Node("negative_hinge_integrable", WithConvex(All("a", P, All("s", P,
                Call("IntegrableOn", Lambda("t", Call("max", Sub(Id("t"), Id("s")), D(0))),
                    Call("Iic", Id("a")), Mu)))),
                "The negative hinge vanishes below s, so its restriction to t <= a is supported inside the compact positive interval between s and a.", true),
            Node("positive_hinge_integrable", WithConvex(All("a", P, All("s", P,
                Call("IntegrableOn", Lambda("t", Call("max", Sub(Id("s"), Id("t")), D(0))),
                    Call("Ioi", Id("a")), Mu)))),
                "The positive hinge vanishes above s. Local finiteness suffices even when the positive tail has infinite curvature mass.", true),
            Node("scalar_hinge_representation", WithConvex(All("a", P, All("s", P,
                Eqn(V("s"), Representation(Id("a"), Id("s")))))),
                "Both finite-interval identities combine into the full scalar formula. The negative branch is Iic a and the positive branch is Ioi a. On the positive subtype these are respectively (0,a] and (a,infinity).", true),
            Node("scalar_hinge_at_one", WithConvex(All("s", Real(), Imp(Ltqn(D(0), Id("s")),
                Eqn(V("s"), Representation(D(1), Id("s")))))),
                "At base one, the affine term is f(1)+r(1)(s-1). The atom at one belongs to the negative branch. For abs(s-1), this is the convention consistent with right derivative one and curvature twice the Dirac mass at one.", true),
            Node("perspective_positive", WithConvex(All("u", Real(), All("v", Real(),
                Imp(Ltqn(D(0), Id("u")), Imp(Ltqn(D(0), Id("v")),
                    Eqn(Mul(Id("v"), Call("f", Call("div", Id("u"), Id("v")))),
                        Add(Add(Add(Mul(Call("f", D(1)), Id("v")),
                            Mul(Call("rightDeriv", Id("f"), D(1)), Sub(Id("u"), Id("v")))),
                            Integral(Call("Iic", D(1)), Call("max", Sub(Mul(Id("t"), Id("v")), Id("u")), D(0)))),
                            Integral(Call("Ioi", D(1)), Call("max", Sub(Id("u"), Mul(Id("t"), Id("v"))), D(0)))))))))),
                "Positive scaling of the proved scalar identity gives the actual perspective in the open quadrant. Axis values and arbitrary-test cost integration require separate endpoint and integration results; they are not assumptions or conclusions of this theorem.", true)
        )));

    private static Formula Representation(Formula a, Formula s) =>
        Add(Add(Add(Call("f", a), Mul(Call("rightDeriv", Id("f"), a), Sub(s, a))),
            Integral(Call("Iic", a), Call("max", Sub(Id("t"), s), D(0)))),
            Integral(Call("Ioi", a), Call("max", Sub(s, Id("t")), D(0))));
    private static Formula WithConvex(Formula body) => All("f", Fn, All("h", Convex, body));
    private static DocumentBlock Node(string name, Formula formula, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("curvaturehingerepresentation-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name.Replace(".", "")))), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Lambda(string name, Formula body) => Seq(Id(name), Sp, Mapsto, Sp, Par(body));
    private static Formula Arrow(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Par(b));
    private static Formula Leqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ltqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Add, Par(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Subtract, Par(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Multiply, Par(b));
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Integral(Formula domain, Formula body) =>
        Seq(Int, Underscore, Grp(Seq(Id("t"), Sp, InMacro, Sp, domain)), Sp, Par(body), Sp,
            Call("dcurvature", Id("h")), Id("t"));
}
