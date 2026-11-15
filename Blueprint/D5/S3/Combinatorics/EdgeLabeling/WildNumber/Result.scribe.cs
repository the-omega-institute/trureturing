using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling.WildNumber;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/andersfostergreenwoodgarciakrawzik2025wildnumber");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every greedy output on the star family has an additive gap r.", H("Result"), Blocks(
            Describe.Lean(DescribeId.Create("wild-number-result-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.claim"), H("claim"),
                StatementSource.FromAuthor(Disp(Seq(Word("claim"), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp, Word("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Leq, Sp, Word("r"), Sp, To, Sp, Exists, Sp, Word("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Exists, Sp, Word("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Parenthesized(Seq(Word("Fin"), Sp, Word("n"))), Sp, Comma, Sp, Exists, Sp, GammaLower, Sp, Colon, Sp, Word("G"), Sp, Dot, Sp, Word("edgeSet"), Sp, To, Sp, Word("Fin"), Sp, D(4), Sp, Comma, Sp, Word("G"), Sp, Dot, Sp, Word("Connected"), Sp, Land, Sp, Word("Function"), Sp, Dot, Sp, Word("Surjective"), Sp, GammaLower, Sp, Land, Sp, Word("wildNumber"), Sp, Word("G"), Sp, GammaLower, Sp, Eq, Sp, D(5), Sp, Star, Sp, Word("r"), Sp, Land, Sp, Parenthesized(Seq(Exists, Sp, Word("W"), Sp, Comma, Sp, Word("IsGreedyOutput"), Sp, Word("G"), Sp, GammaLower, Sp, Word("W"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Word("W"), Sp, Comma, Sp, Word("IsGreedyOutput"), Sp, Word("G"), Sp, GammaLower, Sp, Word("W"), Sp, To, Sp, Word("W"), Sp, Dot, Sp, Word("card"), Sp, Eq, Sp, D(6), Sp, Star, Sp, Word("r")))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Section 7, PDF page 21: “How far off can Algorithm 5.10 be from the actual wild number? Is it ever off by more than one? or two?. . .” The graph is finite, connected, and colored surjectively with Fin 4. Every possible output has 6r edges and the minimum color-connecting size is 5r."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wild-number-result-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.result"), H("result"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Word("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Leq, Sp, Word("r"), Sp, To, Sp, Exists, Sp, Word("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Exists, Sp, Word("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Parenthesized(Seq(Word("Fin"), Sp, Word("n"))), Sp, Comma, Sp, Exists, Sp, GammaLower, Sp, Colon, Sp, Word("G"), Sp, Dot, Sp, Word("edgeSet"), Sp, To, Sp, Word("Fin"), Sp, D(4), Sp, Comma, Sp, Word("G"), Sp, Dot, Sp, Word("Connected"), Sp, Land, Sp, Word("Function"), Sp, Dot, Sp, Word("Surjective"), Sp, GammaLower, Sp, Land, Sp, Word("wildNumber"), Sp, Word("G"), Sp, GammaLower, Sp, Eq, Sp, D(5), Sp, Star, Sp, Word("r"), Sp, Land, Sp, Parenthesized(Seq(Exists, Sp, Word("W"), Sp, Comma, Sp, Word("IsGreedyOutput"), Sp, Word("G"), Sp, GammaLower, Sp, Word("W"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Word("W"), Sp, Comma, Sp, Word("IsGreedyOutput"), Sp, Word("G"), Sp, GammaLower, Sp, Word("W"), Sp, To, Sp, Word("W"), Sp, Dot, Sp, Word("card"), Sp, Eq, Sp, D(6), Sp, Star, Sp, Word("r")))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Section 7, PDF page 21: “How far off can Algorithm 5.10 be from the actual wild number? Is it ever off by more than one? or two?. . .” The graph is finite, connected, and colored surjectively with Fin 4. Every possible output has 6r edges and the minimum color-connecting size is 5r."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("anders-foster-greenwood-garcia-krawzik-2025-wild-number-greedy-gap"), ResolutionKind.Proved)))));

    private static Formula Word(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
