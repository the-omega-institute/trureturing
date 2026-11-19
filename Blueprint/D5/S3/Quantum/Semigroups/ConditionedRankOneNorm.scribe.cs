using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class ConditionedRankOneNormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clipped weights attain the sharp condition-constrained complex essential-sup bound for positive rank-one evolutions.",
        H("Sharp conditioned rank-one optimization"), Blocks(
            Paragraph(Text("Let mu be an arbitrary nonzero finite measure on a measurable space X. "
                + "The real function h is essentially bounded and strictly positive almost everywhere. "
                + "Write H=lpNorm(h,infinity,mu)>0 and Q=integral(h squared)>0. Atomic measures are included. "
                + "All operator inputs are complex; no spatial attainment of H or positive essential floor of h is assumed. "
                + "The rank-one map is P f=h integral(h f)/Q, and T_a=a I+(1-a)P for 0<=a<=1. "
                + "This is a variational synthesis from essential-sup bounds and Bochner integral comparison. "
                + "External novelty and current openness of this formula are unverified.")),
            Entry("weight", "Weight", "Every equivalent positive weight", WeightFormula(),
                "Weight consists of essential boundedness of g and 1/g and strict positivity almost everywhere. MemLp includes AE strong measurability; all measurable weights are included."),
            Entry("condition", "condition", "The multiplication condition number", ConditionFormula(),
                "The product is invariant under positive scalar rescaling."),
            Entry("evolve", "evolve", "Complex rank-one evolution", EvolveFormula(),
                "Evolve(mu,h,a,f) uses the actual complex integral and its real squared normalization Q. The theorem proves Q positive before dividing."),
            Entry("sharp", "Sharp", "All inputs and an attaining witness", SharpFormula(),
                "Sharp uses genuine eLpNorm inequalities for every bounded complex L2 input and an actual attaining input of weighted norm one. It is not defined by the scalar formula."),
            Entry("clipped", "clipped", "The clipped feasible weight", ClippedFormula(),
                "For the theorem parameters 1/kappa<=g star<=1 and 1<=1/g star<=kappa almost everywhere. Its condition number can be strictly below kappa, for example for constant h."),
            Entry("optimum", "optimum", "The explicit optimum value", OptimumFormula(),
                "Q is the integral of h squared and H is the actual lpNorm of h at infinity. The deficit is the integral of h times max(H/kappa-h,0)."),
            Entry("envelope", "envelope", "The all-weight essential envelope", EnvelopeFormula(),
                "Writing G=norm infinity g, B=norm infinity 1/g and c=norm infinity gh, H<=Bc, gh<=c and g<=G with GB<=kappa force c/g>=max(h,H/kappa). No point attaining H is assumed.", true),
            Entry("fixed", "fixed_weight", "The genuine fixed-weight sharp norm", FixedFormula(),
                "The complex integral modulus bound proves the estimate for every input. The actual input f=1/g belongs to L2 and L infinity, has weighted norm one, and attains a+(1-a)c integral(h/g)/Q. An affine essential-sup identity supplies equality.", true),
            Entry("minimum", "conditioned_optimum", "Sharp minimum, excess and all minimizers", MinimumFormula(),
                "The same clipped weight attains the minimum for every a. The excess is exactly (1-a)/Q times the integral of h times absolute(c/g-max(h,H/kappa)). Integral-zero rigidity makes all minimizers for a<1 positive scalar multiples of the clipped weight modulo AE equality. For a<1 the minimum equals one exactly when h>=H/kappa almost everywhere. At a=1 every admissible weight has sharp constant one. This weighted L1 identity gives no L infinity stability estimate. The actual interval semigroup consumes the theorem in its owner. A distinct finite atomic check on a two-point space with counting measure uses a=0, h=(1/4,1), kappa=2 and projection optimum 18/17.", true))));

    private static Formula WeightFormula() => Base(All("g", RF,
        Iff(W(V("g")), And(Bounded(V("g")), And(Bounded(Inv(V("g"))), Pos(V("g")))))));
    private static Formula ConditionFormula() => Base(All("g", RF,
        Eqn(K(V("g")), Mul(Top(V("g")), Top(Inv(V("g")))))));
    private static Formula EvolveFormula()
    {
        Formula integral = Integral(Map("y", V("X"),
            Mul(Call("ofReal", At(V("h"), V("y"))), At(V("f"), V("y")))));
        Formula projection = Div(Mul(Call("ofReal", At(V("h"), V("x"))), integral), Call("ofReal", Q));
        Formula body = Eqn(At(Evolve(), V("x")), Add(Mul(Call("ofReal", V("a")), At(V("f"), V("x"))),
            Mul(Sub(D(1), Call("ofReal", V("a"))), projection)));
        return Params(All("a", Real, All("f", CF, All("x", V("X"), body))));
    }
    private static Formula SharpFormula() => Params(All("a", Real, All("g", RF, All("C", Real,
        Iff(S(V("g"), V("C")), SharpBody())))));
    private static Formula ClippedFormula()
    {
        Formula body = Eqn(At(Call("clipped", V("h"), V("H"), V("kappa")), V("x")),
            Call("inv", Call("max", D(1), Div(Mul(V("kappa"), At(V("h"), V("x"))), V("H")))));
        return Params(All("H", Real, All("kappa", Real, All("x", V("X"), body))));
    }
    private static Formula OptimumFormula() => Params(All("a", Real, All("kappa", Real,
        Eqn(O, Add(D(1), Mul(Div(Sub(D(1), V("a")), Q), Deficit))))));
    private static Formula EnvelopeFormula()
    {
        Formula hypothesis = And(Call("NeZero", V("mu")), Bounded(V("h")));
        hypothesis = And(hypothesis, And(W(V("g")), And(Le(D(1), V("kappa")), Le(K(V("g")), V("kappa")))));
        Formula result = AE("x", Le(Vee, Div(C(V("g")), At(V("g"), V("x")))));
        return Params(All("g", RF, All("kappa", Real, Imp(hypothesis, result))));
    }
    private static Formula FixedFormula()
    {
        Formula hypothesis = And(Hyp, And(W(V("g")), And(Le(D(0), V("a")), Le(V("a"), D(1)))));
        Formula coefficient = Add(V("a"), Div(Mul(Mul(Sub(D(1), V("a")), C(V("g"))), J(V("g"))), Q));
        return Params(All("g", RF, All("a", Real, Imp(hypothesis, S(V("g"), coefficient)))));
    }
    private static Formula MinimumFormula()
    {
        Formula scalarEquality = AE("x", Eqn(At(V("g"), V("x")), Mul(V("s"), At(StarWeight, V("x")))));
        Formula minimizers = Imp(Lt(V("a"), D(1)), Iff(Eqn(V("C"), O),
            Ex("s", Real, And(Lt(D(0), V("s")), scalarEquality))));
        Formula excess = Eqn(Sub(V("C"), O), Mul(Div(Sub(D(1), V("a")), Q), Excess));
        Formula floor = Imp(Lt(V("a"), D(1)), Iff(Eqn(O, D(1)), AE("x", Le(Div(Hh, V("kappa")), At(V("h"), V("x"))))));
        Formula endpoint = Imp(Eqn(V("a"), D(1)), Eqn(V("C"), D(1)));
        Formula tail = And(excess, And(minimizers, And(endpoint, floor)));
        Formula witnessBody = And(S(V("g"), V("C")), And(Le(O, V("C")), tail));
        Formula witness = Ex("C", Real, witnessBody);
        Formula universal = All("g", RF, Imp(And(W(V("g")), Le(K(V("g")), V("kappa"))), witness));
        Formula result = And(W(StarWeight), And(Le(K(StarWeight), V("kappa")), And(S(StarWeight, O), universal)));
        Formula hypothesis = And(Hyp, And(Le(D(1), V("kappa")), And(Le(D(0), V("a")), Le(V("a"), D(1)))));
        return Params(All("kappa", Real, All("a", Real, Imp(hypothesis, result))));
    }

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string prose,
        bool theorem = false) => Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall, Sp, V(x), Colon, Sp, t, Comma, Sp, b);
    private static Formula Ex(string x, Formula t, Formula b) => Seq(Exists, Sp, V(x), Colon, Sp, t, Comma, Sp, b);
    private static Formula Map(string x, Formula t, Formula b) => Seq(Open, V(x), Colon, Sp, t, Close, Mapsto, Sp, b);
    private static Formula Rel(Formula a, FormulaRelationOperator o, Formula b) => new Formula.Relation(a, o, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator o, Formula b) => new Formula.Logic(Par(a), o, Par(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Bin(Formula a, FormulaBinaryOperator o, Formula b) => new Formula.Binary(a, o, b);
    private static Formula Add(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => Call("divide", a, b);
    private static Formula At(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), To, Sp, b);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula RF => Arrow(V("X"), Real);
    private static Formula CF => Arrow(V("X"), Complex);
    private static Formula Base(Formula b) => All("X", Call("Type"), Seq(OpenBracket, Call("MeasurableSpace", V("X")), CloseBracket,
        All("mu", Call("Measure", V("X")), b)));
    private static Formula Params(Formula b) => Base(All("h", RF, b));
    private static Formula Bounded(Formula f) => Call("MemLp", f, Infty, V("mu"));
    private static Formula AE(string x, Formula b) => Call("AE", V("mu"), Map(x, V("X"), b));
    private static Formula Pos(Formula f) => AE("x", Lt(D(0), At(f, V("x"))));
    private static Formula Inv(Formula f) => Map("x", V("X"), Call("inv", At(f, V("x"))));
    private static Formula Top(Formula f) => Call("lpNorm", f, Infty, V("mu"));
    private static Formula W(Formula g) => Call("Weight", V("mu"), g);
    private static Formula K(Formula g) => Call("condition", V("mu"), g);
    private static Formula Hh => Top(V("h"));
    private static Formula Integral(Formula f) => Call("integral", f, V("mu"));
    private static Formula Q => Integral(Map("x", V("X"), new Formula.Power(At(V("h"), V("x")), D(2))));
    private static Formula C(Formula g) => Top(Map("x", V("X"), Mul(At(g, V("x")), At(V("h"), V("x")))));
    private static Formula J(Formula g) => Integral(Map("x", V("X"), Div(At(V("h"), V("x")), At(g, V("x")))));
    private static Formula Vee => Call("max", At(V("h"), V("x")), Div(Hh, V("kappa")));
    private static Formula StarWeight => Call("clipped", V("h"), Hh, V("kappa"));
    private static Formula O => Call("optimum", V("mu"), V("h"), V("a"), V("kappa"));
    private static Formula Hyp => And(Call("IsFiniteMeasure", V("mu")),
        And(Call("NeZero", V("mu")), And(Bounded(V("h")), Pos(V("h")))));
    private static Formula Evolve() => Call("evolve", V("mu"), V("h"), V("a"), V("f"));
    private static Formula S(Formula g, Formula c) => Call("Sharp", V("mu"), V("h"), V("a"), g, c);
    private static Formula Deficit => Integral(Map("x", V("X"), Mul(At(V("h"), V("x")),
        Call("max", Sub(Div(Hh, V("kappa")), At(V("h"), V("x"))), D(0)))));
    private static Formula Excess => Integral(Map("x", V("X"), Mul(At(V("h"), V("x")),
        Call("abs", Sub(Div(C(V("g")), At(V("g"), V("x"))), Vee)))));
    private static Formula Weighted(Formula f) => Map("x", V("X"), Mul(Call("ofReal", At(V("g"), V("x"))), At(f, V("x"))));
    private static Formula Norm(Formula f) => Call("eLpNorm", f, Infty, V("mu"));
    private static Formula Input(Formula f) => And(Bounded(f), Call("MemLp", f, D(2), V("mu")));
    private static Formula Bound => Le(Norm(Weighted(Evolve())), Mul(Call("ofReal", V("C")), Norm(Weighted(V("f")))));
    private static Formula SharpBody() => And(Le(D(0), V("C")), And(All("f", CF, Imp(Input(V("f")), Bound)),
        Ex("f", CF, And(Input(V("f")), And(Eqn(Norm(Weighted(V("f"))), D(1)),
            Eqn(Norm(Weighted(Evolve())), Call("ofReal", V("C"))))))));
}
