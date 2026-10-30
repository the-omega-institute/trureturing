using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class MinimalFlowDilationMixingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expanding covariance of a compact minimal real flow forces topological mixing of the expanding map.",
        H("Mixing from an Expanding Minimal Real Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimal-real-flow-dilation-mixing"),
                DeclarationHandle.Create("D5/S1/Dynamics/MinimalFlowDilationMixing.minimal_real_flow_dilation_mixing"),
                H("Every sufficiently large iterate meets each pair of nonempty open sets"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a compact Hausdorff topological space with an additive action alpha of the real numbers. "
                        + "The action is jointly continuous and minimal: the orbit of every point is dense in X. "
                        + "Let a be a real number greater than one and f a continuous map from X to itself satisfying "
                        + "f(alpha(t,x)) = alpha(a*t,f(x)) for all real t and all x in X. "
                        + "For every pair U,V of nonempty open subsets of X there is a natural N such that, "
                        + "for every natural n at least N, some x in U has f iterated n times at x in V. "
                        + "The witness x may depend on n. No global nonemptiness of X is assumed; the open-set assertion is vacuous on the empty space.")),
                    Paragraph(Text(
                        "Choose u in U. Continuity of the orbit map at time zero gives a positive epsilon such that "
                        + "alpha(s,u) belongs to U whenever the absolute value of s is less than epsilon. "
                        + "Minimality makes translates of V cover X. Compactness and Mathlib's IsCompact.exists_finite_cover_vadd "
                        + "give a finite set I of translating times. If z = alpha(s,v) for s in I and v in V, "
                        + "then alpha(-s,z) = v. Thus the sum M of the absolute values of times in I bounds a hitting time "
                        + "for every z in X. The minus sign converts a covering translate into a hitting time.")),
                    Paragraph(Text(
                        "Induction gives f^n(alpha(s,u)) = alpha(a^n*s,f^n(u)). "
                        + "Since a is greater than one, Mathlib's tendsto_pow_atTop_atTop_of_one_lt makes M/a^n less than epsilon "
                        + "for every sufficiently large n. For each such n choose a bounded hitting time t for f^n(u). "
                        + "The point alpha(t/a^n,u) lies in U and its nth iterate is alpha(t,f^n(u)), which lies in V. "
                        + "The uniform bound over all z is what gives every sufficiently large n.")),
                    Paragraph(Text(
                        "For the actual dyadic inverse limit DyadicSolenoid of DyadicTimeSeparation, take "
                        + "alpha(t,x) = realFlow(t) + x, a = 2 and f(x) = 2 times x in the additive group. "
                        + "The public dyadic_time_separation theorem supplies compactness and the continuous dense-range realFlow, "
                        + "whose nth circle coordinate is t/2^n modulo one. The inherited product topology is Hausdorff. "
                        + "Translation by x is a homeomorphism, so composing it with the dense-range realFlow makes every orbit dense. "
                        + "The homomorphism law makes alpha an additive real action; its continuity is joint. "
                        + "Doubling is continuous and realFlow(2*t) = 2 times realFlow(t), giving the exact expanding covariance. "
                        + "Consequently doubling on this dyadic solenoid is topologically mixing in the displayed all-sufficiently-large-n sense. "
                        + "This exact application is checked with a local action instance, without changing the solenoid's public action instances "
                        + "or retaining a named specialization.")),
                    Paragraph(Text(
                        "The conclusion concerns topological mixing of the discrete map f. "
                        + "It assumes no group structure on X, freeness of the real action, surjectivity or invertibility of f. "
                        + "It makes no entropy, periodic-point or chaos assertion and does not assert that the real flow is mixing. "
                        + "The compact Hausdorff and continuity-of-f hypotheses are retained in the declared theorem; "
                        + "the argument uses compactness, minimality, action continuity and expanding covariance. "
                        + "The searched pinned Dynamics minimality and transitivity APIs do not supply this all-large-iterate implication. "
                        + "This is a repository proof of the displayed inference, with no claim of novelty in the literature."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Conj(params Formula[] xs) => xs.Length == 1 ? xs[0] : And(xs[0], Conj(xs[1..]));

    private static Formula Statement()
    {
        var x = V("X");
        var alpha = V("alpha");
        var f = V("f");
        var a = V("a");
        var point = V("x");
        var covariance = All("t", V("R"), All("x", x,
            Rel(Call("f", Call("alpha", V("t"), point)), FormulaRelationOperator.Equal,
                Call("alpha", new Formula.Binary(a, FormulaBinaryOperator.Multiply, V("t")), Call("f", point)))));
        var witness = Ex("x", x, And(Rel(point, FormulaRelationOperator.MemberOf, V("U")),
            Rel(Call("iterate", f, V("n"), point), FormulaRelationOperator.MemberOf, V("V"))));
        var eventual = Ex("N", V("Nat"), All("n", V("Nat"),
            Imp(Rel(V("N"), FormulaRelationOperator.LessThanOrEqual, V("n")), witness)));
        var openPair = Conj(Call("IsOpen", V("U")), Call("Nonempty", V("U")),
            Call("IsOpen", V("V")), Call("Nonempty", V("V")));
        var mixing = All("U", Call("Set", x), All("V", Call("Set", x), Imp(openPair, eventual)));
        return Disp(All("X", V("Type"), All("alpha", Call("RealAction", x),
            All("a", V("R"), All("f", Call("SelfMap", x),
                Imp(Conj(Call("CompactHausdorff", x), Call("JointlyContinuous", alpha),
                    Call("Minimal", alpha), Rel(D(1), FormulaRelationOperator.LessThan, a),
                    Call("Continuous", f), covariance), mixing))))));
    }
}
