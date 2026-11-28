using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.OrbitClosure;

internal sealed class WordBallTentDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(params Formula[] parts)
    {
        Formula result = Seq(Open, parts[0], Close);
        for (var i = 1; i < parts.Length; i++)
            result = new Formula.Logic(result, FormulaLogicOperator.And,
                Seq(Open, parts[i], Close));
        return result;
    }
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Open, premise, Close, Sp, Rightarrow, Sp, conclusion);
    private static Formula At(string f, Formula x) => C(f, x);
    private static Formula Act(Formula g, Formula x) => C("smul", g, x);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Leq(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Abs(Formula x) => Seq(Bar, x, Bar);
    private static Formula Ratio(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));

    public DocumentDefinition Create()
    {
        var gType = V("G");
        var xType = V("X");
        var real = Seq(Mathbb, Grp(V("R")));
        var nat = Seq(Mathbb, Grp(V("N")));
        var type = Seq(Operatorname, Grp(V("Type")));
        var maps = C("ContinuousMap", xType, real);
        var classes = Seq(
            OpenBracket, C("Group", gType), CloseBracket, Sp,
            OpenBracket, C("MetricSpace", xType), CloseBracket, Sp,
            OpenBracket, C("CompactSpace", xType), CloseBracket, Sp,
            OpenBracket, C("MulAction", gType, xType), CloseBracket, Comma, Sp);
        var hypotheses = And(
            C("InverseClosed", V("S")), C("Generates", V("S")),
            All("g", gType, C("Continuous", C("actionSlice", V("g")))),
            C("Infinite", C("permutationImage", gType, xType)),
            Leq(D(1), V("R")));
        var range = All("x", xType,
            And(Leq(D(0), At("u", V("x"))), Leq(At("u", V("x")), D(1))));
        var defect = All("s", gType, Imp(
            Seq(V("s"), Sp, InMacro, Sp, V("S")),
            All("x", xType, Leq(
                Abs(Seq(At("u", Act(V("s"), V("x"))), Minus, At("u", V("x")))),
                Ratio(D(1), V("R"))))));
        var invariant = All("g", gType, All("x", xType,
            Eqn(At("v", Act(V("g"), V("x"))), At("v", V("x")))));
        var separation = All("v", maps, Imp(invariant,
            Leq(Ratio(D(1), D(2)), C("supnorm", Seq(V("u"), Minus, V("v"))))));
        var conclusion = Some("u", maps, Some("b", xType, Some("h", gType,
            And(range, Eqn(At("u", V("b")), D(1)),
                Eqn(At("u", Act(V("h"), V("b"))), D(0)), defect, separation))));
        var statement = All("G", type, All("X", type, Seq(classes,
            All("S", C("Finset", gType), All("R", nat, Imp(hypotheses, conclusion))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Infinite-image finitely generated continuous actions have bounded continuous tents with arbitrarily small generator defects and fixed orbit oscillation.",
            H("Continuous Word-Ball Tents"),
            Blocks(Describe.Lean(
                DescribeId.Create("infinite-image-continuous-word-ball-tents"),
                DeclarationHandle.Create("D5/S1/Dynamics/OrbitClosure/WordBallTent."
                    + "exists_continuous_wordBall_tent"),
                H("One almost-invariant function with full orbit oscillation"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Topology/petkovic2026cohomology")),
                Blocks(
                    Paragraph(Text("G and X range over independent universes. The finite set S is inverse closed: s in S implies its inverse lies in S. "
                        + "Generates(S) means that the subgroup closure of S is all of G. The notation smul(g,x) is the given action, "
                        + "actionSlice(g) is x mapped to g acting on x, and permutationImage(G,X) is the range of MulAction.toPermHom for this action. "
                        + "Only each individual action slice is assumed continuous; there is no topology on G. ContinuousMap(X,R) denotes real-valued continuous functions, "
                        + "and supnorm is their usual supremum norm on the same compact metric space. The natural R in the denominator is cast to the real numbers.")),
                    Paragraph(Text("For each positive natural R, the same function u satisfies every displayed clause. The points b and h acting on b lie in one actual orbit, "
                        + "with values 1 and 0 respectively. The generator estimate holds at every point for every generator simultaneously. The final quantifier ranges over "
                        + "every continuous invariant real function for this same action. In particular the conclusion includes the source's radii R at least 2.")),
                    Paragraph(Text("First suppose a finite set B of group elements covers every orbit from its base point. Then each orbit is finite with cardinality at most card(B). "
                        + "A homomorphism from G to any fixed finite symmetric group is determined by its values on S, so there are finitely many such homomorphisms. "
                        + "Intersect their kernels for all orbit sizes at most card(B). The intersection has finite index and acts trivially on every orbit, "
                        + "as seen by transporting the actual action on each orbit to a finite labelled set. The permutation image is therefore finite. "
                        + "Contraposition supplies a single point b and a point z=h acting on b outside the finite orbit ball B_R acting on b. "
                        + "This argument includes infinite orbits directly and finite orbits of unbounded sizes; it does not infer that each orbit is infinite.")),
                    Paragraph(Text("Let B_R consist of products of at most R letters from S. Recursive finite unions and images construct this finite ball; "
                        + "the checked word representation identifies membership with word length at most R. The identity belongs to B_R even when S is empty. "
                        + "For each g in B_R, the point g inverse acting on z differs from b. These form a finite closed set F disjoint from {b}. "
                        + "Urysohn separation gives a continuous phi with values in [0,1], value 1 at b and value 0 on F.")),
                    Paragraph(Text("Write tau(g)=max(0,1-length(g)/R), and define u(y) as the maximum over g in B_R of tau(g) times phi(g inverse acting on y). "
                        + "The finite maximum is continuous and lies in [0,1]. Its identity term gives u(b)=1, and every term vanishes at z. "
                        + "Outside B_R the weight is zero, so the same maximum bounds every transported term indexed by any group element.")),
                    Paragraph(Text("For s in S, set k=s inverse times g. The length bound length(k) at most length(g)+1 gives tau(g) at most tau(k)+1/R. "
                        + "The action identity identifies phi(g inverse acting on s acting on y) with phi(k inverse acting on y). "
                        + "Multiplication by a number in [0,1] and the maximum bound give u(s acting on y) at most u(y)+1/R. "
                        + "Apply this also to s inverse and s acting on y for the reverse inequality. No separation between supports or assumption about stabilizers is needed.")),
                    Paragraph(Text("An invariant v has v(b)=v(z). Evaluating u-v at these two points bounds both absolute values |1-v(b)| and |v(b)| by its supremum norm, "
                        + "forcing that norm to be at least 1/2. Identity generators are allowed and have zero defect. Empty S together with the generation hypothesis "
                        + "forces a trivial group, contradicting infinite image. Empty X likewise cannot satisfy infinite image. No additional nonemptiness premise is needed.")),
                    Paragraph(Text("Petkovic's orbit lemmas, Construction con:tent and Lemma lem:tent-properties supply the continuous weighted-maximum mechanism. "
                        + "Finite separation of the transported endpoint replaces the source's choice of a metric bump radius and an endpoint at exact orbit distance R+1. "
                        + "These functions obstruct a uniform supremum-norm estimate of distance to invariants by generator defects. They give no derivative control, "
                        + "no smooth transfer theorem and no resolution of the simultaneous-Diophantine smooth stability conjecture, including its non-linearizable necessity direction."))),
                DescribeRole.Theorem))));
    }
}
