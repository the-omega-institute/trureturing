using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalBlindCounterfactualDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, F.Lt, Sp, b);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Instances(Formula body) => Seq(
        OpenBracket, C("NormedAddCommGroup", V("V")), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, V("V")), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, V("V")), CloseBracket, Sp,
        OpenBracket, C("AddCommGroup", V("O")), CloseBracket, Sp,
        OpenBracket, C("Module", R, V("O")), CloseBracket, Sp, body);
    private static Formula Conj(params Formula[] xs)
    {
        Formula result = xs[^1];
        for (int i = xs.Length - 2; i >= 0; --i) result = And(xs[i], result);
        return result;
    }

    public DocumentDefinition Create()
    {
        Formula cone = V("C"), unit = V("u"), z = V("z"), w = V("w"), e = V("e"), f = V("f"), t = V("T");
        Formula dual = C("LinearMap", R, V("V"), R);
        Formula k = C("base", cone, unit), interior = C("interior", cone);
        Formula plus = Seq(w, Plus, e, Cdot, Sp, z), minus = Seq(w, Minus, e, Cdot, Sp, z);
        Formula strict = All("x", V("V"), Imp(In(V("x"), cone),
            Imp(Ne(V("x"), D(0)), Lt(D(0), App(unit, V("x"))))));
        Formula result = Ex("w", V("V"), Ex("e", R, Ex("f", dual, Conj(
            In(w, k), In(w, interior), Lt(D(0), e), C("proper", cone, unit, f),
            In(plus, k), In(minus, k), In(plus, interior), In(minus, interior),
            Ne(plus, minus), Eq(App(t, plus), App(t, minus)),
            Lt(D(0), Seq(App(f, plus), Minus, App(f, minus)))))));
        Formula directions = Imp(Ne(z, D(0)), Imp(Eq(App(unit, z), D(0)),
            Imp(Eq(App(t, z), D(0)), result)));
        Formula readouts = All("T", C("LinearMap", R, V("V"), V("O")),
            All("z", V("V"), directions));
        Formula assumptions = Imp(C("IsClosed", cone), Imp(strict,
            Imp(Eq(C("span", R, cone), C("top")), readouts)));
        Formula coneAndUnit = All("C", C("PointedCone", R, V("V")),
            All("u", dual, assumptions));
        Formula statement = All("V", V("Type"), All("O", V("Type"), Instances(coneAndUnit)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every nonzero original normalized blind direction has two actual interior states and a distinguishing full proper effect.",
            H("Original blind directions and actual counterfactual states"), Blocks(
                Paragraph(Text("Let C be a closed generating cone in a finite dimensional real normed space V, with a real-linear unit u strictly positive on every nonzero cone vector. The base K is the entire set C intersect {u=1}; proper(C,u,f) means 0<=f(v)<=u(v) for every original cone vector v. The norm only presents the finite dimensional topology. The conclusion specifies original vectors and original effects, without introducing an inner product or replacing either full domain.")),
                Describe.Lean(DescribeId.Create("original-blind-direction-counterfactual"),
                    DeclarationHandle.Create("D5/S3/Quantum/Foundation/OriginalBlindCounterfactual.original_blind_direction_counterfactual"),
                    H("Two interior states share the blind readout and remain distinguishable"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For every real-linear readout T into any real module O and every nonzero z with u(z)=0 and T(z)=0, there are an original normalized interior center w, a strictly positive real scale e, and an original full proper effect f. Both w+e*z and w-e*z belong to K and to the cone interior, are distinct, and have equal T-readouts. Their f-readout difference is strictly positive. No finite-output, injectivity, positivity or operational realizability assumption is made about T.")),
                        Paragraph(Text("Generatingness gives nonempty cone interior. A nonzero interior vector normalizes to an interior member of K. Continuity of both signed lines through this center supplies one strictly positive common scale for the two perturbations. The same unit vanishes on z, so normalization is preserved on both sides.")),
                        Paragraph(Text("Compactness bounds the norm of every point of the entire K by one positive R. A norm-one dual functional l with l(z)=norm(z) gives f=u/2+l/(2R). Its values on every pure point lie in [0,1], so the original cone bound extends these inequalities to the whole C. Since u(z)=0, f(z)>0. The signed perturbations therefore have strictly positive readout difference 2*e*f(z). This constructs a globally proper separator rather than treating the nonpositive signed vector as a state.")),
                        Paragraph(Text("For a triple of original face readouts, a nonzero signed vector in their common kernel and in ker(u) satisfies these hypotheses. The result supplies actual normalized states witnessing failure of separation. The existence and algebra of those original readouts, the assertion that their blind kernel lies in ker(u), six-block norm bounds, and a common pairing require their own hypotheses and proofs. The result asserts no Jordan classification, reciprocal confirmation, or physical implementation."))), DescribeRole.Theorem))));
    }
}
