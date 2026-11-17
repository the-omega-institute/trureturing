using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class InvolutionEvenCyclesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu1990pfaffian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered perfect matchings correspond to actual even-cycle permutations by rooted interlacing.",
        H("Rooted Interlacing of Two Perfect Matchings"),
        Blocks(
            Paragraph(Text("In an arbitrary universe, let X be any finite linearly ordered type. Perm(X) denotes Equiv.Perm X. The input uses the existing "
                + "D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution X: "
                + "its elements are exactly permutations p satisfying p(p(x)) = x and p(x) ≠ x for all x. "
                + "Connected(s,t,x,y) is the existing reflexive transitive closure of s-edges and t-edges. "
                + "SameCycle uses the full integer-power orbit, including singleton product orbits. "
                + "Products act from right to left; the even-position product is t*s.")),
            Paragraph(Text("componentRoot(s,t,x) is the least vertex of the actual component through x. "
                + "firstPhase(s,t,x) means that x is in the full t*s orbit of this minimum. "
                + "Both matching edges exchange its two product-orbit classes, by InvolutionOrbitSplit. "
                + "interlace(s,t) follows s in firstPhase and t outside it; its predecessor follows t "
                + "in firstPhase and s outside it. The root therefore first follows the FIRST input color s. "
                + "This convention is fixed by the supplied order and is unrelated to numeric label parity.")),
            Describe.Lean(DescribeId.Create("rooted-interlacing"),
                DeclarationHandle.Create(Prefix + "rooted_interlacing"),
                H("Full Component Coverage and Ordered Recovery"),
                StatementSource.FromAuthor(Interlacing()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The actual component splits into two disjoint product orbits. "
                    + "Natural powers enumerate each finite full orbit. Interlacing their vertices as "
                    + "r^k(m), s(r^k(m)) covers the entire component, with no repeated orientation choice. "
                    + "The one-step action changes phase, so a returning cycle has even length. "
                    + "The square orbit of the resulting permutation at the same minimum is precisely "
                    + "the first product orbit; alternating successor and predecessor recovers both original mates. "
                    + "The formula quantifies every minimum m of an actual component and every natural k."))),
                DescribeRole.Theorem),
            Paragraph(Text("For an arbitrary output q, cycleRoot(q,x) is the least vertex of its full cycle. "
                + "cyclePhase(q,x) means (q^2).SameCycle(cycleRoot(q,x),x). "
                + "The output subtype requires BOTH no fixed point and even support cardinality for every "
                + "member of q.cycleFactorsFinset. Fixed-point exclusion is essential: that finset omits "
                + "singleton cycles. On this subtype the even cycle period prevents adjacent vertices "
                + "from lying in the same square orbit. Consequently cyclePhase flips at both successor "
                + "and predecessor, including across the last-to-first edge.")),
            Describe.Lean(DescribeId.Create("rooted-reconstruction"),
                DeclarationHandle.Create(Prefix + "rooted_reconstruction"),
                H("Reconstructing the Entire Original Permutation"),
                StatementSource.FromAuthor(Reconstruction()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("recover(q) has first mate q(x) at even rooted distance and q inverse(x) "
                    + "at odd rooted distance; the second mate uses the opposite choices. Both are "
                    + "fixed-point-free involutions. Their actual components equal the full q-cycles, "
                    + "their component minima are the same cycle minima, and their first product orbit "
                    + "equals the original square orbit. Applying forward therefore returns q itself."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rooted-equivalence"),
                DeclarationHandle.Create(Prefix + "equivalence"),
                H("The Actual Equivalence"), StatementSource.FromAuthor(EquivalenceFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The forward function is forward(s,t), with underlying permutation "
                    + "interlace(s,t). The inverse function is recover. The two preceding theorems supply "
                    + "the exact left and right inverse laws of this Equiv. No cardinality argument or "
                    + "arbitrary equipotence is used. All finite X are included, without Nonempty, "
                    + "Inhabited or an even-cardinality input hypothesis. On the empty type the maps "
                    + "are the unique empty permutations. On odd cardinalities both admissible carriers "
                    + "are empty. A common matching pair is a genuine transposition; when s=t, "
                    + "interlace(s,s)=s. On two-cycles the recovered mates coincide. Longer cycles retain "
                    + "the ordered color distinction and disconnected components are rooted separately."))),
                DescribeRole.Definition),
            Paragraph(Text("Literature: Eğecioğlu, Skew-symmetric matrices and the Pfaffian, "
                + "Ars Combinatoria 29, 107–116, sections 1.2–1.3 and the bijection proof; "
                + "Library/Combinatorics/egecioglu1990pfaffian.md. The paper labels the incoming edge "
                + "at the minimum alpha; this construction instead explicitly follows its first input "
                + "outward from the minimum. No equality of these phase conventions is asserted. "
                + "This structural equivalence proves no weighted matching-sign identity, "
                + "Pfaffian determinant-square formula, embedding theorem or complexity bound.")))));

    private static Formula V(string x) => F.Id(x);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Fn(string x, Formula type, Formula body) =>
        Seq(Open, V(x), Colon, Sp, type, Close, Sp, Mapsto, Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LessOrEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula X() => V("X");
    private static Formula Perm() => Call("Perm", X());
    private static Formula Matching() => Call("FixedPointFreeInvolution", X());
    private static Formula Pair(Formula a, Formula b) => Call("pair", a, b);
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula App(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Q() => Call("interlace", V("s"), V("t"));
    private static Formula R(Formula x) => Call("componentRoot", V("s"), V("t"), x);
    private static Formula P(Formula x) => Call("firstPhase", V("s"), V("t"), x);
    private static Formula C(Formula x, Formula y) =>
        Call("Connected", Val(V("s")), Val(V("t")), x, y);
    private static Formula Pow(Formula f, Formula k, Formula x) => App(new Formula.Power(f, k), x);
    private static Formula Choice(Formula p, Formula a, Formula b) => Call("ite", p, a, b);
    private static Formula Inv(Formula q) => Call("inv", q);
    private static Formula Context(Formula body) => All("X", V("Type"),
        All("finite", Call("Fintype", X()), All("order", Call("LinearOrder", X()), body)));
    private static Formula EvenPermType()
    {
        var q = V("q"); var x = V("x"); var c = V("c");
        var free = All("x", X(), NotEqual(App(q,x),x));
        var even = All("c", Perm(), Imp(Member(c, Call("cycleFactorsFinset",q)),
            Call("Even", Call("card", Call("support",c)))));
        return Call("Subtype", Fn("q", Perm(), And(free,even)));
    }

    private static Formula Interlacing()
    {
        var x = V("x"); var y = V("y"); var m = V("m"); var k = V("k");
        var product = Multiply(Val(V("t")), Val(V("s")));
        var powers = And(Equal(Pow(Q(), Multiply(Num(2), k), m), Pow(product, k, m)),
            Equal(Pow(Q(), Add(Multiply(Num(2), k), Num(1)), m),
                App(Val(V("s")), Pow(product, k, m))));
        var pointwise = All("x", X(), And(
            Equal(App(Q(), x), Choice(P(x), App(Val(V("s")), x), App(Val(V("t")), x))),
            And(Equal(App(Inv(Q()), x), Choice(P(x), App(Val(V("t")), x), App(Val(V("s")), x))),
                Iff(Call("cyclePhase", Q(), x), P(x)))));
        var pair = Pair(V("s"),V("t"));
        var recovery = Equal(Call("recover", Call("forward",pair)), pair);
        var graph = All("x", X(), All("y", X(), Iff(Call("SameCycle",Q(),x,y),C(x,y))));
        var root = All("x", X(), And(C(x,R(x)), All("y", X(), Imp(C(x,y),LessOrEqual(R(x),y)))));
        var rootedPowers = All("m", X(), Imp(All("y", X(), Imp(C(m,y),LessOrEqual(m,y))),
            All("k", V("Nat"),powers)));
        return Disp(Context(All("s", Matching(), All("t", Matching(),
            And(recovery, And(graph, And(root, And(rootedPowers,pointwise))))))));
    }

    private static Formula Reconstruction()
    {
        var q = Val(V("q")); var x = V("x"); var pair = Call("recover", V("q"));
        var phase = Call("cyclePhase", q, x);
        return Disp(Context(All("q", EvenPermType(),
            And(Equal(Call("forward", pair), V("q")), All("x", X(),
                And(Equal(App(Val(Call("fst", pair)), x), Choice(phase, App(q,x), App(Inv(q),x))),
                    Equal(App(Val(Call("snd", pair)), x), Choice(phase, App(Inv(q),x), App(q,x)))))))));
    }

    private static Formula EquivalenceFormula() => Disp(Context(Seq(
        Call("equivalence", X()), Colon, Sp,
        Call("Equiv", Call("Product", Matching(), Matching()), EvenPermType()))));
}
