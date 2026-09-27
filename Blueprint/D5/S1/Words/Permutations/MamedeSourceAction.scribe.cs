using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeSourceActionDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/MamedeSourceAction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mamede2026commutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first-orientation excursion determines the target endpoint and word support.",
        H("Source Excursion and Target Factorization"),
        Blocks(
            Paragraph(Text("Let gamma be the product of the deleted excursion and let "
                + "pi=sigma gamma inverse. The source word used below is an actual "
                + "singleton reduced word with the first-orientation shape, not merely "
                + "an arbitrary factorization of sigma.")),
            Node("deletedExcursion_action", "Action of the deleted excursion", Disp(Q(
                D(1), Le, V("m"), Lt, V("i"), Lt, V("M"), Le, V("n"),
                Land, D(1), Le, V("t"), Le, Q(V("n"), Plus, D(1)),
                Implies, Call("gamma", Call("position", V("n"), V("t"))), Eq,
                Call("position", V("n"), Call("cycleCase", V("m"), V("i"),
                    Q(V("M"), Plus, D(1)), V("t"))))),
                "Here gamma is the product of Deleted(m,M,i). The cycleCase map "
                    + "sends m to i, i to M+1, and M+1 to m, and fixes every other "
                    + "one-based position. The bounds keep these positions distinct.",
                DescribeRole.Theorem),
            Node("source_full_product", "Source and image products", Disp(Q(
                D(1), Le, V("m"), Lt, V("i"), Le, V("j"), Lt, V("M"), Le, V("n"),
                Land, Forall, V("k"), InMacro, V("q"), Comma,
                V("i"), Lt, V("k"), Lt, V("M"),
                Implies,
                Call("prod", V("n"), Call("concat", V("p"),
                    Call("Full", V("m"), V("M"), V("i"), V("j")), V("q"))),
                Eq,
                Call("prod", V("n"), Call("Image", V("i"), V("j"), V("p"), V("q"))),
                Times, Call("prod", V("n"), Call("Deleted", V("m"), V("M"), V("i"))))),
                "The suffix support makes every generator of q commute with the "
                    + "deleted excursion. Splitting the first descent then gives the "
                    + "product identity for any prefix p, without assuming an actual "
                    + "source word or its SourceShape premise.",
                DescribeRole.Theorem),
            Node("source_target_factorization", "Every target singleton factors", Disp(Q(
                Call("ExactSource", V("n"), V("m"), V("M"), V("i"), V("j"), V("sigma")),
                Land, Call("SourceShape", V("m"), V("M"), V("i"), V("j"),
                    V("a0"), V("p0"), V("q0")),
                Land, Call("Singleton", V("n"), V("sigma"), V("a0")),
                Implies, Forall, V("b"), Comma,
                Call("Singleton", V("n"), V("pi"), V("b")), Implies,
                Exists, V("p"), Comma, Exists, V("q"), Comma,
                V("b"), Eq, Call("Image", V("i"), V("j"), V("p"), V("q")),
                Land, Call("PrefixBounds", V("m"), V("j"), V("p")),
                Land, Call("SuffixBounds", V("i"), V("M"), V("q")))),
                "Here pi=sigma gamma inverse. Every singleton reduced target word "
                    + "contains the full descent from j to i; every prefix letter "
                    + "lies strictly between m and j, and every suffix letter strictly "
                    + "between i and M. The source-shape and singleton premises remain live.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("mamede-source-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
