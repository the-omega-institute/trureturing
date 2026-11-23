using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrincipalSpecialization;

internal sealed class AlexanderssonLeiteFundamentalLengthRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/alexanderssonleite2026sinkpolynomials");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The natural unit interval path on four vertices refutes real-rootedness of the weighted fundamental-length image.",
        H("A four-vertex counterexample to Question 6.7"),
        Blocks(
            Describe.Lean(DescribeId.Create("fundamental-length-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The universal real-rootedness claim"),
                StatementSource.FromAuthor(Disp(Seq(Name("claim"), Sp, Leftrightarrow, Sp, Group(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The source uses vertex labels 1 through n. Lean uses Fin n and adds one to "
                        + "each label in the correspondence. An ordered edge satisfies i < j and j ≤ h(i). "
                        + "The graph has the undirected closure of these edges. A proper coloring uses "
                        + "positive integer colors, and its weight is q to the number of ordered edges "
                        + "whose colors strictly increase.")),
                    Paragraph(Text(
                        "The coefficient at a monomial sums the weights of all proper colorings with "
                        + "exactly its actual color multiplicities. Ranking its used colors preserves "
                        + "the multiplicities in increasing color order, properness, and the ascent count. "
                        + "The strict positions of the sorted color word give the proper partial sums "
                        + "of these multiplicities.")),
                    Paragraph(Text(
                        "In degree n the fundamental element F indexed by S has coefficient one at "
                        + "each cut set T containing S. The map Ψ sends F to t to the power |S| + 1. "
                        + "The corresponding weight of cut set T is t to the power |T| + 1 times "
                        + "(1 − t) to the power n − |T| − 1. Summing over the optional cuts gives the "
                        + "prescribed value, and descending through the supersets of S gives uniqueness. "
                        + "The symbol X in the formula is the source alphabet, and t is the polynomial "
                        + "indeterminate. In degree zero Ψ sends 1 to 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fundamental-length-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("The weighted image can have nonreal roots"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Group(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take h = (2, 3, 4, 4) in the source's labels and q = 16. The ordered edges "
                        + "are (1, 2), (2, 3), and (3, 4). Grouping colorings by the number r of colors "
                        + "they use gives a packed coloring sum for each r, multiplied by the factor "
                        + "t to the power r times (1 − t) to the power 4 − r.")),
                    Paragraph(Text(
                        "The weighted sums for two, three, and four colors are 272, 2448, and 7089. "
                        + "Their contribution is t²(272 + 1904t + 4913t²). Removing the two linear "
                        + "factors at zero leaves a quadratic with discriminant −1720128. A real root "
                        + "would make this discriminant a real square."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var h = F.Id("h");
        var i = F.Id("i");
        var q = F.Id("q");
        var fin = Call("Fin", n);
        var hType = Seq(fin, Sp, To, Sp, fin);
        var inflationary = All(i, fin, Seq(i, Sp, Le, Sp, new Formula.Apply(h, [i])));
        var chromatic = new Formula.Apply(new Formula.Subscript(F.Id("X"), new Formula.Subscript(F.Id("H"), h)),
            [F.Id("X"), q]);
        var image = new Formula.Apply(new Formula.Subscript(Name("Psi"), F.Id("t")), [chromatic]);
        var splits = new Formula.Apply(new Formula.Subscript(Name("Splits"), Seq(Mathbb, Grp(F.Id("R")))), [image]);

        return All(n, Seq(Mathbb, Grp(F.Id("N"))),
            Then(Seq(Num(0), Sp, Lt, Sp, n),
                All(h, hType, Then(Call("Monotone", h), Then(inflationary,
                    All(q, Seq(Mathbb, Grp(F.Id("R"))), Then(Seq(Num(0), Sp, Le, Sp, q), splits)))))));
    }

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Group(Seq(variable, Colon, Sp, type)), Comma, Sp, body);

    private static Formula Then(Formula premise, Formula conclusion) =>
        Seq(Group(premise), Sp, Rightarrow, Sp, conclusion);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Name(name), [.. args]);

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Group(Formula body) => Seq(Open, body, Close);
}
