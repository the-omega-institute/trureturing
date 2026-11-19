using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class WordAscentsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/alexanderssonjalquemener2025rook");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict adjacent-ascent count shared by natural-valued word families.",
        H("Strict adjacent ascents of words"),
        Blocks(
            Describe.Lean(DescribeId.Create("ascents"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Permutation/WordAscents.asc"),
                H("Strict adjacent-ascent count"), StatementSource.FromAuthor(F.Disp(Ascents())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every list w of natural numbers, count the indices i in range(length(w) minus one) for which getD(w,i,0) < getD(w,i+1,0). Both queried positions exist for each counted index. Natural subtraction is truncated: empty words and singletons have count zero. Equality is not an ascent. Section 2, page 4 of the cited source uses this strict adjacent comparison. This is the unchanged statistic shared by the multiset rook-Eulerian polynomials and the ordinary ascent-sequence, Dyck and Narayana constructions; it imposes no Ferrers-board, content, avoidance or monotonicity hypothesis."))),
                DescribeRole.Definition)),
        []));

    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula ListN => Call("List", N);
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Lambda(string variable, Formula type, Formula body) =>
        F.Seq(Parenthesized(F.Seq(Id(variable), F.Colon, type)), F.Mapsto, body);
    private static Formula Get(Formula word, Formula index) => Call("getD", word, index, Num(0));
    private static Formula Ascents() => All("w", ListN, Equal(Call("asc", Id("w")),
        Call("card", Call("filter", Call("range", Subtract(Call("length", Id("w")), Num(1))),
            Lambda("i", N, Lt(Get(Id("w"), Id("i")), Get(Id("w"), Add(Id("i"), Num(1)))))))));
}
