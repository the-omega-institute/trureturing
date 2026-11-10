using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class FullRectangularRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A square bound for every state of the actual left corner controls a rectangular product in an arbitrary unital complex C-star algebra.",
        H("Rectangular recovery from corner states"),
        Blocks(
            Theorem("corner-mem-iff", "corner_mem_iff", "The actual corner", Corner(),
                "The complex submodule cornerSpace(e) consists of x with ex=x and xe=x. For a star projection e this is equivalent to x=exe. Its norm, topology and order are inherited from A."),
            Theorem("positive-real", "positive_real", "Self-adjoint values are real", PositiveReal(),
                "A positive continuous complex functional takes a self-adjoint element to a real complex number. The notation re denotes real part and ofReal denotes the real inclusion in Complex."),
            Theorem("positive-re-bounds", "positive_re_bounds", "Order bounds for positive functionals", PositiveBounds(),
                "Applying positivity to the two order-unit bounds for a self-adjoint element bounds its real functional value by its norm times the real unit mass. The functional need not be normalized."),
            Theorem("exists-norming-state", "exists_norming_state", "An internally obtained signed norm-attaining state", Norming(),
                "For each nonzero self-adjoint a, real Hahn-Banach on the inherited real self-adjoint subspace and the norm-additive positive extension theorem give positive functionals p and q. Their masses sum to one. Equality in the two norm bounds forces p(a)=norm(a)p(1) and q(a)=-norm(a)q(1). At least one mass is positive; normalizing that functional gives the displayed state and either spectral sign. No state or norm-attainment premise is supplied."),
            Theorem("norming-state-multiplication", "norming_state_multiplication", "Zero variance gives both multiplication identities", Multiplication(),
                "For the same normalized functional phi, put r=a-s1. Contractivity of the original positive state bound and the C-star identity force phi(r*r)=0. The two positive-functional Cauchy-Schwarz inequalities then give phi(rx)=phi(xr)=0 for every actual middle element x. Both multiplication identities use this one phi."),
            Theorem("norming-state-sandwich", "norming_state_sandwich", "The exact sandwich identity", Sandwich(),
                "Applying the two multiplication identities to a*C and C gives the sandwich formula for every C in the ambient algebra. The two occurrences of phi refer to the same state."),
            Theorem("row-gram-mem", "rowGram_mem", "The row Gram element is in the left corner", RowGram(),
                "If eU=U, taking adjoints gives U-star e=U-star. Consequently U U-star belongs to eAe. This uses the row Gram element, whereas U-star U belongs to the right corner in the rectangular situation."),
            Theorem("full-rectangular-recovery", "full_rectangular_recovery", "Rectangular norm recovery", Recovery(),
                "A has exactly the classes CStarAlgebra A, PartialOrder A and StarOrderedRing A. Let e and f be actual star projections, a self-adjoint with a=eae, and U=eUf. A CornerState(e,he) is a positive continuous complex-linear functional on cornerSpace(e), normalized at the actual unit e. In the display omega(x) abbreviates omega.functional applied to x with its corner-membership proof. Both a and U U-star have that membership. All corner states are quantified, including states without any normality requirement. There is no dimension, nontriviality, invertibility, positivity of a, or supplied norming-state hypothesis.",
                "The a=0 case gives the bound directly. Otherwise an ambient norm-attaining state phi and a nonzero real s are constructed internally. Since ea=a, the multiplication identity gives phi(e)=1. Restricting this same positive continuous phi to the actual corner yields a normalized CornerState, so the all-state premise gives norm(a)^2 <= kappa re(phi(U U-star)). The sandwich identity and the original normalized-state bound give norm(a)^2 re(phi(U U-star)) <= norm(aU)^2. Multiplication and the positive square root yield the displayed inequality.",
                "The zero projections, zero algebra, zero channel, unequal corners and noninvertible channels are included. Positivity and continuity on the inherited corner are the usual mathematical state conditions; normalized positive functionals on a C-star corner are automatically continuous. The argument needs only the restriction of the constructed ambient state, so no ambient extension of an arbitrary corner state is assumed.",
                "For the two-corner application one takes (a,U,kappa)=(sP,T,1) and (sQ,star(T),4). The second row Gram element is star(T)*T and the denominator is two. Deriving those two all-state premises from P2, the separate product estimates, and the resulting uniform stability theorem are additional mathematical steps. This result concerns the fixed C-star elements only and makes no assertion about a physical state source or the origin of quantum theory."))));

    private static DocumentBlock.Describe Theorem(string id, string selector, string title, Formula statement, params string[] prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/FullRectangularRecovery." + selector),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks([.. prose.Select(p => Paragraph(Text(p)))]), DescribeRole.Theorem);

    private static Formula Id(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. args]);
    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Imp(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);
    private static Formula And(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);
    private static Formula Eqn(Formula x, Formula y) => Equal(x, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula NegOf(Formula x) => Subtract(D(0), x);
    private static Formula Norm(Formula x) => Call("norm", x);
    private static Formula Sq(Formula x) => Seq(Open, x, Close, Caret, Grp(D(2)));
    private static Formula ReOf(Formula x) => Call("re", x);
    private static Formula SA(Formula x) => Call("IsSelfAdjoint", x);
    private static Formula PosMap() => Call("PositiveContinuousLinearMap", Call("Complex"), Id("A"), Call("Complex"));
    private static Formula Context(Formula body) => All("A", Seq(Call("Type"), Star),
        Seq(OpenBracket, Call("CStarAlgebra", Id("A")), CloseBracket, Sp,
            OpenBracket, Call("PartialOrder", Id("A")), CloseBracket, Sp,
            OpenBracket, Call("StarOrderedRing", Id("A")), CloseBracket, Sp, body));
    private static Formula Elements(string[] names, Formula body)
    {
        foreach (var n in names.Reverse()) body = All(n, Id("A"), body);
        return body;
    }
    private static Formula Corner() => Context(Elements(["e", "x"],
        Imp(Call("IsStarProjection", Id("e")), new Formula.Logic(
            new Formula.Relation(Id("x"), FormulaRelationOperator.MemberOf, Call("cornerSpace", Id("e"))),
            FormulaLogicOperator.Iff, Eqn(Id("x"), Mul(Mul(Id("e"), Id("x")), Id("e")))))));
    private static Formula PositiveReal() => Context(All("phi", PosMap(), Elements(["a"],
        Imp(SA(Id("a")), Eqn(App(Id("phi"), Id("a")), Call("ofReal", ReOf(App(Id("phi"), Id("a")))))))));
    private static Formula PositiveBounds()
    {
        var bound = Mul(Norm(Id("a")), ReOf(App(Id("phi"), D(1))));
        var value = ReOf(App(Id("phi"), Id("a")));
        return Context(All("phi", PosMap(), Elements(["a"], Imp(SA(Id("a")),
            And(Le(NegOf(bound), value), Le(value, bound))))));
    }
    private static Formula Norming() => Context(Elements(["a"], Imp(SA(Id("a")),
        Imp(new Formula.Relation(Id("a"), FormulaRelationOperator.NotEqual, D(0)),
            Ex("phi", PosMap(), Ex("s", Call("Real"), And(Eqn(App(Id("phi"), D(1)), D(1)),
                And(Eqn(App(Id("phi"), Id("a")), Call("ofReal", Id("s"))), Eqn(Sq(Id("s")), Sq(Norm(Id("a")))))))))));
    private static Formula NormingContext(Formula body) => Context(All("phi", PosMap(),
        Imp(Eqn(App(Id("phi"), D(1)), D(1)), Elements(["a"], Imp(SA(Id("a")),
            All("s", Call("Real"), Imp(Eqn(App(Id("phi"), Id("a")), Call("ofReal", Id("s"))),
                Imp(Eqn(Sq(Id("s")), Sq(Norm(Id("a")))), body))))))));
    private static Formula Multiplication() => NormingContext(Elements(["x"], And(
        Eqn(App(Id("phi"), Mul(Id("a"), Id("x"))), Mul(Call("ofReal", Id("s")), App(Id("phi"), Id("x")))),
        Eqn(App(Id("phi"), Mul(Id("x"), Id("a"))), Mul(Call("ofReal", Id("s")), App(Id("phi"), Id("x")))))));
    private static Formula Sandwich() => NormingContext(Elements(["C"],
        Eqn(App(Id("phi"), Mul(Mul(Id("a"), Id("C")), Id("a"))),
            Mul(Call("ofReal", Sq(Norm(Id("a")))), App(Id("phi"), Id("C"))))));
    private static Formula RowGram() => Context(Elements(["e", "U"], Imp(Call("IsStarProjection", Id("e")),
        Imp(Eqn(Mul(Id("e"), Id("U")), Id("U")), new Formula.Relation(
            Mul(Id("U"), Call("star", Id("U"))), FormulaRelationOperator.MemberOf, Call("cornerSpace", Id("e")))))));
    private static Formula Recovery()
    {
        var e = Id("e"); var f = Id("f"); var a = Id("a"); var u = Id("U"); var k = Id("kappa");
        var omega = Call("functional", Id("omega"));
        var allStates = All("omega", Call("CornerState", e, Id("he")),
            Le(Sq(Norm(App(omega, a))), Mul(k, ReOf(App(omega, Mul(u, Call("star", u)))))));
        return Context(Elements(["e", "f", "a", "U"],
            All("he", Call("IsStarProjection", e), All("hf", Call("IsStarProjection", f),
                Imp(SA(a), Imp(Eqn(a, Mul(Mul(e, a), e)), Imp(Eqn(u, Mul(Mul(e, u), f)),
                    All("kappa", Call("Real"), Imp(Lt(D(0), k), Imp(allStates,
                        Le(Seq(Frac, Grp(Sq(Norm(a))), Grp(Call("sqrt", k))), Norm(Mul(a, u)))))))))))));
    }
}
