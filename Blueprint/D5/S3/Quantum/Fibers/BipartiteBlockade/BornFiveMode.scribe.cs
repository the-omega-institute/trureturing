using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class BornFiveModeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common quantum state supplies the five-mode Born law at a degree-two blocked center.",
        H("Born Five-Mode Recovery"),
        Blocks(Describe.Lean(
            DescribeId.Create("born-five-mode-reconstruction"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Fibers/BipartiteBlockade/BornFiveMode.born_five_mode_reconstruction"),
            H("Two drives recover the local law; occupations alone do not"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let u and w be the two distinct neighbors of v in a finite properly "
                    + "two-colored simple graph. The basis consists of all independent "
                    + "configurations. For any positive semidefinite trace-one complex "
                    + "matrix, push its diagonal Born weights forward to the local words "
                    + "000, 100, 010, 001 and 101. These are five probabilities of one "
                    + "common source. The ordering here places the center at index two.")),
                Paragraph(Text(
                    "Write X=m(u), Y=m(w), Z=m(v), and let beta be the blocker obtained "
                    + "from the original and color-scaled accelerations. The five masses "
                    + "are beta-Z, 1-beta-Y, Z, 1-beta-X and beta-1+X+Y. Thus kappa is "
                    + "beta-1+X+Y and Delta is (1-Z)*kappa-X*Y. Initial off-diagonal "
                    + "coherence is unrestricted. Nonzero central drive suffices for "
                    + "this inverse; positive drives in particular satisfy it.")),
                Paragraph(Text(
                    "Occupations alone have an actual physical ambiguity. One state "
                    + "assigns equal masses to the empty configuration and {u,w}; a "
                    + "second assigns equal masses to {u} and {w}. Both diagonal matrices "
                    + "are positive semidefinite with trace one, and every vertex has "
                    + "the same occupation mean in the two states. Their blocker at v "
                    + "differs. The endpoint pair is independent because its vertices "
                    + "have the same color. This ambiguity is for zero driving settings; "
                    + "it asserts no equality of the acceleration readouts."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Mean(string state, string vertex) =>
        C("occupationMean", V("G"), V(state), V(vertex));
    private static Formula Block(string state) => C("blockadeMean", V("G"), V(state), V("v"));
    private static Formula Law() => C("bornModeLaw", V("G"), V("u"), V("v"), V("w"), V("rho"));
    private static Formula Acc(bool scaled) => C("acceleration", V("G"),
        scaled ? C("colorScaledDrive", V("color"), V("omega")) : V("omega"),
        V("rho"), V("v"));
    private static Formula Beta() => Seq(D(2), Mean("rho", "v"), Plus,
        C("if", C("color", V("v")),
            new Formula.Fraction(Seq(Acc(true), Minus, D(2), Acc(false)),
                Seq(D(4), C("omega", V("v")), Caret, D(2))),
            new Formula.Fraction(Seq(D(2), Acc(false), Minus, Acc(true)),
                Seq(D(2), C("omega", V("v")), Caret, D(2)))));

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, V("V"), Colon, Sp, C("Type"), Comma, Sp,
        OpenBracket, C("Fintype", V("V")), CloseBracket, Sp,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
        V("G"), Colon, Sp, C("SimpleGraph", V("V")), Comma, Sp,
        V("u"), Comma, Sp, V("v"), Comma, Sp, V("w"), Colon, Sp, V("V"), Comma, Sp,
        V("color"), Colon, Sp, V("V"), Rightarrow, Sp, C("Bool"), Comma, Sp,
        V("omega"), Colon, Sp, V("V"), Rightarrow, Sp, C("Real"), Comma, Sp,
        V("rho"), Colon, Sp, C("Matrix", C("Configuration", V("G")),
            C("Configuration", V("G")), C("Complex")), Comma, Sp,
        C("neighbors", V("G"), V("v")), Sp, Eq, Sp, C("pair", V("u"), V("w")),
        Sp, Land, Sp, V("u"), Sp, Neq, Sp, V("w"), Sp, Land, Sp,
        C("properColoring", V("G"), V("color")), Sp, Land, Sp,
        C("omega", V("v")), Sp, Neq, Sp, D(0), Sp, Land, Sp,
        C("PosSemidef", V("rho")), Sp, Land, Sp, Eqn(C("trace", V("rho")), D(1)),
        Rightarrow, Sp,
        C("nonnegative", Law()), Sp, Land, Sp,
        Eqn(C("sum", Law()), D(1)), Sp, Land, Sp,
        Eqn(Law(), C("vector",
            Seq(Beta(), Minus, Mean("rho", "v")),
            Seq(D(1), Minus, Beta(), Minus, Mean("rho", "w")),
            Mean("rho", "v"),
            Seq(D(1), Minus, Beta(), Minus, Mean("rho", "u")),
            Seq(Beta(), Minus, D(1), Plus, Mean("rho", "u"), Plus, Mean("rho", "w")))),
        Sp, Land, Sp, Exists, Sp, V("sigma"), Comma, Sp, V("tau"), Colon, Sp,
        C("Matrix", C("Configuration", V("G")), C("Configuration", V("G")), C("Complex")),
        Comma, Sp, C("PosSemidef", V("sigma")), Sp, Land, Sp,
        Eqn(C("trace", V("sigma")), D(1)), Sp, Land, Sp,
        C("PosSemidef", V("tau")), Sp, Land, Sp,
        Eqn(C("trace", V("tau")), D(1)), Sp, Land, Sp,
        Open, Forall, Sp, V("x"), Colon, Sp, V("V"), Comma, Sp,
        Eqn(Mean("sigma", "x"), Mean("tau", "x")), Close, Sp, Land, Sp,
        Block("sigma"), Sp, Neq, Sp, Block("tau"), Dot));
}
