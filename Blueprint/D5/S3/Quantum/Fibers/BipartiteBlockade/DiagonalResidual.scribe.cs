using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class DiagonalResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fibers/BipartiteBlockade/DiagonalResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A diagonal correlation direction compatible with one bipartite acceleration experiment.",
        H("A Diagonal Correlation Residual"),
        Blocks(Describe.Lean(
            DescribeId.Create("diagonal-residual-of-distinct-neighborhoods"),
            DeclarationHandle.Create(Prefix + "diagonal_residual_of_distinct_neighborhoods"),
            H("Two different nonlinear neighborhoods produce a residual direction"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a finite simple graph with a proper Boolean coloring, and let "
                    + "every drive be nonzero. Suppose u and w have distinct open neighborhoods, "
                    + "each of size at least two. There is a signed measure on the actual "
                    + "independent configurations whose total mass and all single-site "
                    + "occupation means vanish. At least one blocking mean changes, while "
                    + "the signed sum of the blocking means weighted by the squared drives "
                    + "vanishes.")),
                Paragraph(Text(
                    "For a neighborhood N, assign (-1) raised to the cardinality of S to "
                    + "each subconfiguration S of N and assign zero elsewhere. This measure "
                    + "has zero mass and zero single-site means. Its blocking moment at v "
                    + "is one exactly when N is contained in the open neighborhood of v.")),
                Paragraph(Text(
                    "All vertices whose neighborhoods contain a fixed nonempty N have the "
                    + "same color. Consequently the signed squared-drive coefficient of "
                    + "this measure is nonzero. Two such measures can be combined to cancel "
                    + "that coefficient. Ordering the two distinct neighborhoods so that "
                    + "the second is not contained in the first ensures that a blocking "
                    + "moment of the resulting measure remains nonzero. This is a signed "
                    + "diagonal perturbation; positivity of density matrices requires a "
                    + "separate small-perturbation argument."))),
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

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, V("V"), Colon, Sp, C("Type"), Comma, Sp,
        OpenBracket, C("Fintype", V("V")), CloseBracket, Sp,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
        V("G"), Colon, Sp, C("SimpleGraph", V("V")), Comma, Sp,
        V("color"), Colon, Sp, V("V"), To, C("Bool"), Comma, Sp,
        V("drive"), Colon, Sp, V("V"), To, C("Real"), Comma, Sp,
        V("u"), Comma, Sp, V("w"), Colon, Sp, V("V"), Comma, Sp,
        C("proper", V("G"), V("color")), Land, Sp,
        Open, Forall, Sp, V("v"), Comma, Sp, C("drive", V("v")), Neq, Sp, D(0), Close,
        Land, Sp, D(2), Leq, Sp, C("card", C("neighbors", V("G"), V("u"))),
        Land, Sp, D(2), Leq, Sp, C("card", C("neighbors", V("G"), V("w"))),
        Land, Sp, C("neighbors", V("G"), V("u")), Neq, Sp,
        C("neighbors", V("G"), V("w")), Rightarrow, Sp,
        Exists, Sp, V("delta"), Colon, Sp, C("Configuration", V("G")), To, C("Real"), Comma, Sp,
        C("totalMass", V("delta")), Eq, D(0), Land, Sp,
        Open, Forall, Sp, V("v"), Comma, Sp,
        C("occupationMoment", V("G"), V("delta"), V("v")), Eq, D(0), Close,
        Land, Sp, C("signedCompatibility", V("G"), V("color"), V("drive"), V("delta")),
        Eq, D(0), Land, Sp, Exists, Sp, V("v"), Comma, Sp,
        C("blockMoment", V("G"), V("delta"), V("v")), Neq, Sp, D(0), Dot));
}
