using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class EdgeCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWords/EdgeCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural length, the unordered Fibonacci cube edge count equals total "
        + "occupation over legal words and the size-weighted sum of their actual counts.",
        H("Counting legal-word toggle edges by deletion"),
        Blocks(
            Paragraph(Text(
                "A word is a Boolean function on Fin n. Its support in positions 1 through n "
                + "contains i+1 exactly when the value at the zero-based position i is true. "
                + "The existing predicate Adm says that no two consecutive positions are true. "
                + "The existing legalWordGraph is the induced Boolean hypercube on these literal "
                + "words: an unordered edge is a pair whose Hamming distance is one. "
                + "Occupation is the sum of the Boolean values converted to natural numbers, "
                + "hence the size of that same support.")),
            Describe.Lean(DescribeId.Create("legal-words"),
                DeclarationHandle.Create(Prefix + "Legal"), H("The actual legal-word carrier"),
                StatementSource.FromAuthor(LegalFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Legal n is the subtype of Boolean functions on Fin n satisfying Adm. "
                    + "It includes the unique empty word when n is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-support-count"),
                DeclarationHandle.Create(Prefix + "supportCount"), H("Counting occupation fibers"),
                StatementSource.FromAuthor(SupportCountFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "supportCount n k is the cardinality of the finite set of actual legal words "
                    + "of length n whose occupation is k. It is not an independently specified "
                    + "sequence. All counts use the same word carrier as the graph."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("edge-count"),
                DeclarationHandle.Create(Prefix + "edge_count"), H("Two counts of the same edges"),
                StatementSource.FromAuthor(EdgeCountFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/klavzar2013structure")),
                Blocks(Paragraph(Text(
                    "For every natural n, the cardinality of the native unordered edge finset "
                    + "equals the sum of occupation over all Legal n words. That same sum equals "
                    + "the sum of k times supportCount n k, for k from zero through the integer "
                    + "quotient of n+1 by two, inclusive. There are no additional count hypotheses.")),
                    Paragraph(Text(
                        "Delete an occupied position from a legal word. Deletion preserves "
                        + "legality, changes exactly one coordinate, and reduces occupation by one. "
                        + "Two such deletion pairs cannot define the same unordered edge unless "
                        + "both the larger word and the deleted position agree: swapping the "
                        + "endpoints would force occupation to decrease in both directions. "
                        + "Conversely, a Hamming-one edge has a unique differing coordinate; its "
                        + "true endpoint and that coordinate recover the deletion pair. This "
                        + "bijection gives the first equality. Partitioning the same words by "
                        + "occupation gives the second. The existing sharp occupation bound "
                        + "ensures that all fibers lie within the stated cutoff.")),
                    Paragraph(Text(
                        "At length zero, the deletion-pair type and the edge set are empty, "
                        + "and both occupation sums vanish. The binomial formula for individual "
                        + "fibers, the observation-kernel dimensions, and exact-sequence claims "
                        + "are outside this statement."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Word(Formula n) => new Formula.TypeArrow(Fin(n), Call("Bool"));
    private static Formula LegalType(Formula n) => Seq(OpenBrace, F.Id("w"), Colon, Sp, Word(n),
        Sp, Mid, Sp, Call("Adm", n, F.Id("w")), CloseBrace);
    private static Formula Value(Formula b) => Call("val", b);
    private static Formula Occupation(Formula b) => Call("occupationCount", b);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(F.Id(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula FilterCard(Formula n, Formula k) => QCall("Finset", "card",
        QCall("Finset", "filter",
            LambdaOf("b", LegalType(n), Eq(Occupation(Value(F.Id("b"))), k)),
            QCall("Finset", "univ", LegalType(n))));

    private static Formula LegalFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", Nat(), Eq(Call("Legal", n), LegalType(n))));
    }

    private static Formula SupportCountFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        return Disp(All("n", Nat(), All("k", Nat(),
            Eq(Call("supportCount", n, k), FilterCard(n, k)))));
    }

    private static Formula EdgeCountFormula()
    {
        Formula n = F.Id("n");
        Formula graphCard = QCall("Finset", "card",
            QCall("SimpleGraph", "edgeFinset", Call("legalWordGraph", n)));
        Formula occupationSum = SumOver("b", LegalType(n), Occupation(Value(F.Id("b"))));
        Formula groupedSum = SumOver("k", QCall("Finset", "range", Add(Call("div", Add(n, D(1)), D(2)), D(1))),
            Mul(F.Id("k"), Call("supportCount", n, F.Id("k"))));
        return Disp(All("n", Nat(), And(Eq(graphCard, occupationSum), Eq(occupationSum, groupedSum))));
    }
}
