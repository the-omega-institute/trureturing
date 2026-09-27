using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Equality;

internal sealed class FiberwiseEqualDistanceLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.";

    private static readonly Formula Wv = F.Id("w"), Zv = F.Id("z"), Lab = LambdaLower;
    private static readonly Formula RhoP = Seq(Widetilde, Grp(F.Rho));

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
        Formula prob = Seq(F.Rho, Comma, Sp, F.Id("Q"), Sp, F.Text, Grp(Sp, F.Id("probability"), Sp, F.Id("laws"),
            Sp, F.Id("on"), Sp), F.Id("W"), Comma, Sp, F.Id("Z"), Comma, Sp, F.Id("P"), Sp, Eq, Sp, Push(F.Rho));
        Formula support = Seq(Forall, Sp, Zv, Comma, Sp, F.Id("Q"), Open, Zv, Close, Sp, Gt, Sp, D(0), Sp,
            Rightarrow, Sp, Exists, Sp, Wv, Comma, Sp, Lab, Open, Wv, Close, Sp, Eq, Sp, Zv);
        Formula liftable = Seq(Exists, Sp, RhoP, Sp, F.Text, Grp(Sp, F.Id("probability"), Sp), Comma, Sp,
            Push(RhoP), Sp, Eq, Sp, F.Id("Q"));
        Formula close = Seq(Exists, Sp, RhoP, Sp, F.Text, Grp(Sp, F.Id("probability"), Sp), Comma, Sp,
            Push(RhoP), Sp, Eq, Sp, F.Id("Q"), Sp, Land, Sp, Tv(F.Rho, RhoP), Sp, Eq, Sp,
            Tv(F.Id("P"), F.Id("Q")));
        return Disp(Seq(
            prob, Sp, Rightarrow, RowBreak, Grp(),
            Open, liftable, Close, Sp, Iff, Sp, Open, support, Close, Sp, Land, RowBreak, Grp(),
            Open, support, Close, Sp, Rightarrow, Sp, close, Dot));
    }

    private static Formula Push(Formula law) => Seq(Sub(Lab, Star), Sp, law);

    private static Formula Tv(Formula a, Formula b) =>
        Seq(Operatorname, Grp(F.Id("TV")), Open, a, Comma, Sp, b, Close);

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));

    private static Formula Sub(Formula baseFormula, Formula index) => Seq(baseFormula, Underscore, Grp(index));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("fiber-lift-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
