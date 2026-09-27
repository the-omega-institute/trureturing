using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Equality;

internal sealed class FiberwiseEqualDistanceLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.";

    private static readonly Formula Wv = F.Id("w"), Zv = F.Id("z"), Lab = LambdaLower;
    private static readonly Formula RhoP = Seq(F.Rho, Apos);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prescribed label law Q lifts to a world law exactly when every label of positive Q-mass has a nonempty "
            + "fiber, and then some lift is as close to the original world law as Q is to its label law.",
        H("Lifting a Label Law at Equal Total-Variation Distance"),
        Blocks(
            Node("kernel", "The label kernel",
                Disp(Seq(Sub("K", Seq(Wv, Comma, Zv)), Sp, Eq, Sp, OpenBracket, Lab, Open, Wv, Close, Sp, Eq, Sp, Zv,
                    CloseBracket)),
                "The deterministic kernel of the label map; applying it to a world law gives the pushforward label "
                    + "law.",
                "labelKernel", DescribeRole.Definition),
            Node("lift", "Equal-distance lift", TheoremFormula(),
                "Let rho be a probability law on the finite world W, lambda : W -> Z a label map, P the pushforward "
                    + "of rho and Q a probability law on Z. A lift of Q puts mass Q(z) on the fiber of z, so labels "
                    + "of positive Q-mass need nonempty fibers. Conversely, on a fiber with P(z) > 0 put "
                    + "tilde-rho(w) = Q(z) rho(w) / P(z), and on a fiber with P(z) = 0 put the mass Q(z) on one chosen "
                    + "element. This is a probability law with pushforward Q. On a fiber with P(z) > 0 all changes "
                    + "have the sign of Q(z) - P(z), and on a fiber with P(z) = 0 the law rho vanishes, so mass only "
                    + "increases. No fiber mixes an increase with a decrease, and the equality criterion for "
                    + "total-variation contraction under a channel gives TV(rho, tilde-rho) = TV(P, Q).",
                "fiberwise_equal_distance_lift", DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula rhoType = Arrow(F.Id("W"), reals);
        Formula qType = Arrow(F.Id("Z"), reals);
        Formula rhoNonnegative = ForallNonnegative(Wv, F.Rho);
        Formula rhoNormalized = SumEqualsOne(Wv, F.Rho, "W");
        Formula qNonnegative = ForallNonnegative(Zv, F.Id("Q"));
        Formula qNormalized = SumEqualsOne(Zv, F.Id("Q"), "Z");
        Formula support = Seq(Forall, Sp, Zv, Comma, Sp, F.Id("Q"), Open, Zv, Close, Sp, Gt, Sp, D(0), Sp,
            Rightarrow, Sp, Exists, Sp, Wv, Comma, Sp, Lab, Open, Wv, Close, Sp, Eq, Sp, Zv);
        Formula liftable = ExistsLift(RhoP, F.Id("Q"), includeDistance: false);
        Formula close = ExistsLift(RhoP, F.Id("Q"), includeDistance: true);
        Formula body = Seq(
            Open, Open, liftable, Close, Sp, Iff, Sp, Open, support, Close, Close, Sp, Land, RowBreak, Grp(),
            Open, Open, support, Close, Sp, Rightarrow, Sp, close, Close, Dot);
        Formula quantified = Seq(
            Forall, Sp, F.Id("W"), Comma, Sp, F.Id("Z"), Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("Fintype", F.Id("W")), CloseBracket, Sp,
            OpenBracket, Call("Fintype", F.Id("Z")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("Z")), CloseBracket, Sp,
            Forall, Sp, F.Rho, Colon, Sp, rhoType, Comma, Sp,
            Implies(rhoNonnegative, Implies(rhoNormalized,
                Seq(Forall, Sp, Lab, Colon, Sp, Arrow(F.Id("W"), F.Id("Z")), Comma, Sp,
                    Forall, Sp, F.Id("Q"), Colon, Sp, qType, Comma, Sp,
                    Implies(qNonnegative, Implies(qNormalized, body))))));
        return Disp(quantified);
    }

    private static Formula ForallNonnegative(Formula variable, Formula law) =>
        Seq(Forall, Sp, variable, Comma, Sp, D(0), Sp, Leq, Sp,
            law, Open, variable, Close);

    private static Formula SumEqualsOne(Formula variable, Formula law, string typeName) =>
        Seq(new Formula.Subscript(Sum, variable), Sp, law, Open, variable, Close,
            Sp, Eq, Sp, D(1));

    private static Formula ExistsLift(Formula rhoPrime, Formula q, bool includeDistance)
    {
        Formula probability = And(
            ForallNonnegative(Wv, rhoPrime),
            And(SumEqualsOne(Wv, rhoPrime, "W"),
                includeDistance
                    ? And(Equal(Output(rhoPrime), q),
                        Equal(Tv(F.Rho, rhoPrime), Tv(Output(F.Rho), q)))
                    : Equal(Output(rhoPrime), q)));
        return Seq(Exists, Sp, rhoPrime, Colon, Sp, Arrow(F.Id("W"), Seq(Mathbb, Grp(F.Id("R")))), Comma, Sp,
            probability);
    }

    private static Formula Output(Formula law) =>
        Call("channelOutput", Call("labelKernel", Lab), law);

    private static Formula Arrow(Formula left, Formula right) =>
        Seq(left, Sp, To, Sp, right);

    private static Formula Paren(Formula value) => Seq(Open, value, Close);

    private static Formula And(Formula left, Formula right) =>
        Seq(Paren(left), Sp, Land, Sp, Paren(right));

    private static Formula Implies(Formula left, Formula right) =>
        Seq(Paren(left), Sp, Rightarrow, Sp, Paren(right));

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula Tv(Formula a, Formula b) =>
        Seq(Operatorname, Grp(F.Id("TV")), Open, a, Comma, Sp, b, Close);

    private static Formula Sub(string name, Formula index) =>
        Seq(F.Id(name), Underscore, Grp(index));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("fiber-lift-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
