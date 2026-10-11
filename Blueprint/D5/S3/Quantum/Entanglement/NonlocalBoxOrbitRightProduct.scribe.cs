using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class NonlocalBoxOrbitRightProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/botteron2024nonlocalboxorbit");
    private const string Conjecture =
        "We conjecture that the same result actually holds without the tilde, i.e. the right multiplication P^{\\boxtimes k} gives the highest CHSH-value of \\mathrm{Orbit}^{(k)}(P), as observed numerically.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right multiplication maximizes CHSH over every parenthesization in the PR-SR-I triangle.",
        H("Right multiplication maximizes CHSH over the orbit"),
        Blocks(
            Node("PR", "Popescu-Rohrlich box", BoxValue("PR", If(Equal(Add(V("a"), V("b")),
                Mul(V("x"), V("y"))), Fraction(1, 2), D(0))),
                "Introduction, displayed definitions of PR, I, P0 and P1: PR(a,b|x,y) := (1/2) 1[a XOR b = xy]. Bits are Fin 2: addition and multiplication are modulo two, and the four arguments are a,b,x,y in that order. The displayed conditional has real values.", Literature),
            Node("P0", "Constant-zero shared output", BoxValue("P0", If(And(
                Equal(V("a"), D(0)), Equal(V("b"), D(0))), D(1), D(0))),
                "Introduction, displayed definitions of PR, I, P0 and P1: P0 := 1[a=b=0]. The conditional ignores both input bits.", Literature),
            Node("P1", "Constant-one shared output", BoxValue("P1", If(And(
                Equal(V("a"), D(1)), Equal(V("b"), D(1))), D(1), D(0))),
                "Introduction, displayed definitions of PR, I, P0 and P1: P1 := 1[a=b=1]. The conditional ignores both input bits.", Literature),
            Node("SR", "Shared randomness", Disp(Equal(Call("SR"),
                Seq(Fraction(1, 2), Sp, Cdot, Sp, Parenthesized(Add(Call("P0"), Call("P1")))))),
                "Section 2.5, p. 17: SR := (P0 + P1)/2 is the shared randomness box. The real scalar acts pointwise on the function.", Literature),
            Node("Ibox", "Uniform box", BoxValue("Ibox", Fraction(1, 4)),
                "Introduction, displayed definitions of PR, I, P0 and P1: I := 1/4. Ibox is its Lean name; every conditional probability has the same real value.", Literature),
            Node("boxProd", "The WBS box product", ProductFormula(),
                "Equation (9) is the sum over a1,a2,b1,b2 of the two box probabilities and the two output indicators. For the wiring W_BS in Section 4, f1=x, g1=y, f2=x a1, g2=y b1, f3=a1 XOR a2 and g3=b1 XOR b2. The displayed finite sums use the literal product of the two output conditionals; the external arguments are a,b,x,y. Each sum ranges over Fin 2, and its value is real.", Literature),
            Node("chsh", "CHSH winning probability", ChshFormula(),
                "Section 2.3, p. 15: CHSH(P) := one quarter of the sum of P(a,b|x,y) over a XOR b = xy. The final sum is filtered by precisely that equation; all four bits range over Fin 2. This is the winning-probability normalization, rather than the correlator normalization.", Literature),
            Node("Paren", "Full binary parenthesizations", Disp(Seq(Call("Paren"), Sp, Colon, Sp,
                Call("Type"), Sp, SemiSpace, Call("Paren.leaf"), Sp, Colon, Sp, Call("Paren"),
                Sp, SemiSpace, Call("Paren.node"), Sp, Colon, Sp,
                Arrow(Call("Paren"), Arrow(Call("Paren"), Call("Paren"))))),
                "A full binary parenthesization has either one leaf or an ordered pair of child parenthesizations. The constructors leaf and node carry no labels: every leaf stands for the same box P.", AssessedProvenance.FromRepo()),
            Node("Paren.size", "Leaf count", Disp(All("l", Call("Paren"), All("r", Call("Paren"),
                And(Equal(Call("Paren.size", Call("Paren.leaf")), D(1)),
                    Equal(Call("Paren.size", Call("Paren.node", V("l"), V("r"))),
                        Add(Call("Paren.size", V("l")), Call("Paren.size", V("r")))))))),
                "The leaf count is one at a leaf and the sum of both child counts at a node. It counts copies of P, not internal multiplication nodes.", AssessedProvenance.FromRepo()),
            Node("eval", "Evaluate a parenthesization", Disp(All("P", BoxType(),
                All("l", Call("Paren"), All("r", Call("Paren"), And(
                    Equal(Call("eval", V("P"), Call("Paren.leaf")), V("P")),
                    Equal(Call("eval", V("P"), Call("Paren.node", V("l"), V("r"))),
                        Call("boxProd", Call("eval", V("P"), V("l")),
                            Call("eval", V("P"), V("r"))))))))),
                "Evaluation substitutes P at every leaf and the W_BS product at every internal node. Both subtree evaluations use the same box.", AssessedProvenance.FromRepo()),
            Node("orbit", "Every product of k copies", OrbitFormula(),
                "Section 2.1, p. 12, defines the k-orbit by the words: all possible products with k times the term P, using the multiplication \\boxtimes_W. Q belongs exactly when a full binary tree t has k leaves and Q equals its evaluation. There is no zero-leaf tree, so orbit 0 P is empty.", Literature),
            Node("rightPow", "Multiply fresh copies on the right", RightFormula(),
                "Theorem 13, p. 16, writes P^{boxtimes k} := ((P boxtimes P) boxtimes P) ... boxtimes P. rightPow is this left-nested product: every step multiplies by a fresh P on the right. Its zero-depth value is set to P; that convention has no effect on the empty zero-depth orbit.", Literature),
            Node("claim", "Conjecture 15", Disp(Equal(Call("claim"), Parenthesized(ClaimBody()))),
                "Conjecture 15 (Dyck paths), p. 16, verbatim: " + Conjecture +
                " The source's displayed notation is P^{\\boxtimes k} and \\mathrm{Orbit}^{(k)}(P). The encoding ranges over every real box function P in convexHull Real {PR,SR,Ibox} with chsh P >= 3/4, every natural k >= 2 and every Q in orbit k P. It drops Theorem 13's tilted-orbit distillation hypothesis. Fin 2 implements XOR as modular addition. No restriction is imposed on the full binary parenthesization.", Literature),
            Node("whole_triangle_max", "The whole triangle satisfies the bound", Disp(WholeBody()),
                "For every box in Conv{PR,SR,I}, every parenthesization has CHSH at most the right product at the same leaf count. The conclusion needs neither chsh P >= 3/4 nor a distillation hypothesis, and includes the one-leaf case. In coordinates P=a PR+(u-a) SR+(1-u) I, multiplication sends (u,a),(v,b) to (uv,av+(1+u-2a)b/4), and CHSH is 1/2+(u+a)/4. The region 0<=u<=1, 0<=a<=(1+u)/2 is closed under this map. A root rotation increases the second coordinate while preserving the first. Repeated multiplication by the original box on the right is monotone in the second coordinate. Structural induction straightens every tree to the left-nested right product.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("result", "The right product is maximal", Disp(Call("claim")),
                "The whole-triangle bound implies Conjecture 15. The maximality statement of Theorem 13 extends to the full orbit without its distillation assumption. Maximality alone does not say that the right product improves on P or that communication complexity collapses. Other wirings, boxes outside the triangle and an explicit formula for the exact maximum as a function of k remain separate questions.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("botteron-et-al-2024-nonlocal-box-orbit-right-product"),
                    ResolutionKind.Proved)))));

    private static AssessedProvenance Literature => AssessedProvenance.FromLiterature(Source);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("nonlocal-box-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + (name == "Paren.size" ? "size" : name)), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Op(string name)
    {
        var parts = name.Split('.');
        Formula result = Seq(Operatorname, Grp(V(parts[0])));
        foreach (var part in parts.Skip(1))
            result = Seq(result, Dot, Operatorname, Grp(V(part)));
        return result;
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Op(name)
        : Seq(Op(name), Parenthesized(Seq([.. args.SelectMany((a, i) => i == 0
            ? new[] { a } : new[] { Comma, Sp, a })])));
    private static Formula App(Formula function, params Formula[] args) =>
        Seq(function, Parenthesized(Seq([.. args.SelectMany((a, i) => i == 0
            ? new[] { a } : new[] { Comma, Sp, a })])));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Typed(V(name), type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Typed(V(name), type)), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LessEq(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Rightarrow, Sp, b);
    private static Formula And(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Star, Sp, b);
    private static Formula Fraction(byte a, byte b) => new Formula.Fraction(D(a), D(b));
    private static Formula If(Formula p, Formula a, Formula b) =>
        Seq(Call("if"), Sp, Parenthesized(p), Sp, Call("then"), Sp, a,
            Sp, Call("else"), Sp, b);
    private static Formula BitType() => Call("Fin", D(2));
    private static Formula BoxType() => Arrow(BitType(), Arrow(BitType(), Arrow(BitType(),
        Arrow(BitType(), Seq(Mathbb, Grp(V("R")))))));
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(V("R")));
    private static Formula BoxValue(string name, Formula value) => Disp(All("a", BitType(),
        All("b", BitType(), All("x", BitType(), All("y", BitType(),
            Equal(Call(name, V("a"), V("b"), V("x"), V("y")), value))))));
    private static Formula SumBit(string name, Formula body) => Seq(
        new Formula.Subscript(Sum, Typed(V(name), BitType())), Sp, Parenthesized(body));
    private static Formula ProductFormula() => Disp(All("P", BoxType(), All("Q", BoxType(),
        All("a", BitType(), All("b", BitType(), All("x", BitType(), All("y", BitType(),
            Equal(Call("boxProd", V("P"), V("Q"), V("a"), V("b"), V("x"), V("y")),
                SumBit("a1", SumBit("a2", SumBit("b1", SumBit("b2", Mul(Mul(Mul(
                    App(V("P"), V("a1"), V("b1"), V("x"), V("y")),
                    App(V("Q"), V("a2"), V("b2"), Mul(V("x"), V("a1")), Mul(V("y"), V("b1")))),
                    Parenthesized(If(Equal(V("a"), Add(V("a1"), V("a2"))), D(1), D(0)))),
                    Parenthesized(If(Equal(V("b"), Add(V("b1"), V("b2"))), D(1), D(0))))))))))))))));
    private static Formula ChshFormula() => Disp(All("P", BoxType(), Equal(Call("chsh", V("P")),
        Mul(Fraction(1, 4), SumBit("a", SumBit("b", SumBit("x", Seq(
            new Formula.Subscript(Sum, Seq(Typed(V("y"), BitType()), Comma, Sp,
                Equal(Add(V("a"), V("b")), Mul(V("x"), V("y"))))), Sp,
            App(V("P"), V("a"), V("b"), V("x"), V("y"))))))))));
    private static Formula Hull() => Call("convexHull", RealType(), Seq(OpenBrace,
        Call("PR"), Comma, Sp, Call("SR"), Comma, Sp, Call("Ibox"), CloseBrace));
    private static Formula OrbitFormula() => Disp(All("k", NatType(), All("P", BoxType(),
        Equal(Call("orbit", V("k"), V("P")), Seq(OpenBrace, Typed(V("Q"), BoxType()), Sp, Mid,
            Sp, Ex("t", Call("Paren"), And(Equal(Call("Paren.size", V("t")), V("k")),
                Equal(V("Q"), Call("eval", V("P"), V("t"))))), CloseBrace)))));
    private static Formula RightFormula() => Disp(All("P", BoxType(), All("n", NatType(),
        And(Equal(Call("rightPow", V("P"), D(0)), V("P")), And(
            Equal(Call("rightPow", V("P"), D(1)), V("P")),
            Equal(Call("rightPow", V("P"), Add(V("n"), D(2))), Call("boxProd",
                Call("rightPow", V("P"), Add(V("n"), D(1))), V("P"))))))));
    private static Formula Bound() => LessEq(Call("chsh", V("Q")),
        Call("chsh", Call("rightPow", V("P"), V("k"))));
    private static Formula WholeBody() => All("P", BoxType(), Imp(Member(V("P"), Hull()),
        All("k", NatType(), All("Q", BoxType(), Imp(Member(V("Q"),
            Call("orbit", V("k"), V("P"))), Bound())))));
    private static Formula ClaimBody() => All("P", BoxType(), Imp(Member(V("P"), Hull()),
        Imp(LessEq(Fraction(3, 4), Call("chsh", V("P"))), All("k", NatType(),
            Imp(LessEq(D(2), V("k")), All("Q", BoxType(), Imp(Member(V("Q"),
                Call("orbit", V("k"), V("P"))), Bound())))))));
}
