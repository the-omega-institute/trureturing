using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ExtremalDensity;

internal sealed class RelativeAntiSidorenkoArcCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/ExtremalDensity/RelativeAntiSidorenkoArcCount";
    private const string Slug = "bitonti-hogan-noel-tsarev-2026-question-5-3";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/bitonti2026sidorenko");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected relatively anti-Sidorenko orientation",
        H("A connected relatively anti-Sidorenko orientation"),
        Blocks(Describe.Lean(
            DescribeId.Create("question-five-three"),
            DeclarationHandle.Create(Module + ".question_5_3"),
            H("An affirmative answer to Question 5.3"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Write U(D) for the simple graph obtained by forgetting arc directions. "
                    + "Oriented means the arc relation is asymmetric, which forbids loops and opposing arcs. "
                    + "ArcCount counts ordered adjacent pairs. EdgeCount counts the edges of the underlying "
                    + "simple graph. The two Hom counts are natural cardinalities of all adjacency-preserving "
                    + "vertex maps, including noninjective maps, and are coerced to rationals for the inequality. "
                    + "The Fin labels represent arbitrary finite pattern order. The host carrier V is any finite "
                    + "type, including the empty type, and the host can be disconnected.")),
                Paragraph(Text(
                    "The witness has thirteen vertices and nineteen arcs. Two copies of the four-sign "
                    + "K(2,4) gadget share root 0, and their other terminals are joined by the arc 1→2. "
                    + "Two new leaves form 11→0→12. For each fixed root image, conditioning on the two "
                    + "free terminal images gives exact products of signed neighbor counts for directed maps "
                    + "and of common-neighbor counts for undirected maps. The same branch profile occurs on "
                    + "both sides of the terminal arc, so interchanging the free images averages its two "
                    + "directions while the root remains fixed. Integer AM–GM gives a factor of 256 for "
                    + "each sign gadget, and the two leaves give a factor of four. The product of these "
                    + "three factors and the factor of two for the terminal arc is 2^19.")),
                Paragraph(Text(
                    "Bitonti, Hogan, Noel and Tsarev pose Question 5.3 using Definition 1.2. Nie and Wei "
                    + "give the four-sign gadget and use reversal averaging for an arc between the terminals "
                    + "of one copy. The construction here uses their gadget twice and holds the shared root "
                    + "fixed throughout the averaging."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create(Slug), ResolutionKind.Proved)))));

    private static Formula Statement() =>
        Bind(Exists, "n", Seq(Mathbb, Grp(FormulaDsl.Id("N"))),
            Bind(Exists, "D", Call("Digraph", Call("Fin", FormulaDsl.Id("n"))),
                Seq(Call("Oriented", FormulaDsl.Id("D")), Sp, Land, Sp,
                    Call("Connected", Call("U", FormulaDsl.Id("D"))), Sp, Land, Sp,
                    Call("ArcCount", FormulaDsl.Id("D")), Sp, Call("mod"), Sp, D(4), Sp, Eq, Sp, D(3),
                    Sp, Land, Sp, Open, AllHosts(), Close)));

    private static Formula AllHosts() =>
        Bind(Forall, "V", Call("Type"),
            Seq(OpenBracket, Call("Finite", FormulaDsl.Id("V")), CloseBracket, Sp,
                Bind(Forall, "G", Call("Digraph", FormulaDsl.Id("V")),
                    Seq(Call("Oriented", FormulaDsl.Id("G")), Sp, Implies, Sp,
                        Call("Hom", FormulaDsl.Id("D"), FormulaDsl.Id("G")), Sp, Leq, Sp,
                        Open, Frac, Grp(D(1)), Grp(D(2)), Close,
                        Caret, Grp(Call("EdgeCount", Call("U", FormulaDsl.Id("D")))), Sp, Cdot, Sp,
                        Call("Hom", Call("U", FormulaDsl.Id("D")), Call("U", FormulaDsl.Id("G")))))));

    private static Formula Bind(Formula quantifier, string variable, Formula domain, Formula body) =>
        Seq(quantifier, Sp, FormulaDsl.Id(variable), Colon, Sp, domain, Comma, Sp, body);

    private static Formula Call(string name) => Seq(Operatorname, Grp(FormulaDsl.Id(name)));

    private static Formula Call(string name, Formula argument) => Seq(
        Call(name), Open, argument, Close);

    private static Formula Call(string name, Formula first, Formula second) => Seq(
        Call(name), Open, first, Comma, Sp, second, Close);
}
