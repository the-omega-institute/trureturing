using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class AndrewsHopkinsExcedanceParityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/PermutationPatterns/andrewshopkins2026excedances");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original one-based excedance statistic gives more odd than even partitions at n = 28.",
        H("A counterexample to excedance parity positivity"), Blocks(
            Paragraph(Text("A partition of n is a finite weakly decreasing list of positive integers with sum n. Nat.Partition n stores its multiset of parts with positivity and sum proofs. Sorting in decreasing order identifies this carrier with the original lists, with every multiplicity retained. An excedance is an index i starting at one for which the ith part is strictly greater than i.")),
            Entry("decreasing-parts", "decreasingParts", "The decreasing list of parts", PartsFormula(),
                "For every natural n and partition p of n, decreasingParts sorts the full multiset of parts in weakly decreasing order. There is no bound on the list length or the size of n.", DescribeRole.Definition, true),
            Entry("excedances", "excedances", "One-based excedances", ExcedancesFormula(),
                "The finite index i in Lean starts at zero. Comparing the indexed part with i.val + 1 therefore implements exactly the original one-based inequality. Every index of the decreasing list is considered, including the last index; equality is not an excedance.", DescribeRole.Definition, true),
            Entry("even-count", "evenCount", "The full even carrier", CountFormula("evenCount", "Even"),
                "For every natural n, evenCount is the cardinality of the full subtype of Nat.Partition n on which the original excedance count is even. This is a cardinality of actual partitions, without a generating-function or recurrence definition.", DescribeRole.Definition, true),
            Entry("odd-count", "oddCount", "The full odd carrier", CountFormula("oddCount", "Odd"),
                "For every natural n, oddCount is the cardinality of the full subtype of Nat.Partition n on which the same original excedance count is odd.", DescribeRole.Definition, true),
            Entry("claim", "claim", "The universal positivity assertion", ClaimFormula(),
                "The assertion after Corollary 7 and Table 1 in Section 2 quantifies over every natural n at least 12 and asks whether evenCount n is strictly greater than oddCount n. The original statistic and Table 1 fix the even-minus-odd direction despite the inconsistent even/odd labels in the displayed generating functions of Corollary 7.", DescribeRole.Definition, true),
            Entry("result", "result", "The universal assertion is false", new Formula.Not(Local("claim")),
                "At n = 28, the full even subtype has cardinality 1850 and the full odd subtype has cardinality 1868. Their difference is -18. Hence the strict inequality required by the universal assertion fails. The proof enumerates positive decreasing lists with remaining sum, maximum part and fuel, proves completeness and absence of duplicates, and converts them injectively into actual Nat.Partition values. Completeness follows by sorting an arbitrary partition; positivity bounds its length by its sum and each part by n. Finite subtype cardinalities then equal the filtered enumeration cardinalities. The original Fin-indexed excedance function is evaluated on these actual partitions, and the resulting closed counts are checked by kernel reduction. This establishes a counterexample at 28; it makes no assertion of the globally first counterexample or of worldwide priority.", DescribeRole.Theorem, false,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("andrews-hopkins-2026-excedance-parity-positivity"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string text, DescribeRole role, bool literature, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("andrews-hopkins-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role, resolution);

    private static Formula PartsFormula() => All("n", N(), All("p", Partition(F.Id("n")),
        Equal(At(Local("decreasingParts"), F.Id("p")),
            At(Q("Multiset", "sort"), At(Q("Nat", "Partition", "parts"), F.Id("p")),
                LambdaOf("a", N(), LambdaOf("b", N(), Rel(F.Id("a"), FormulaRelationOperator.GreaterThanOrEqual, F.Id("b"))))))));
    private static Formula ExcedancesFormula() => All("n", N(), All("p", Partition(F.Id("n")),
        Equal(At(Local("excedances"), F.Id("p")), At(Q("Fintype", "card"),
            Subtype("i", At(Q("Fin"), At(Q("List", "length"), At(Local("decreasingParts"), F.Id("p")))),
                Rel(At(Q("List", "get"), At(Local("decreasingParts"), F.Id("p")), F.Id("i")),
                    FormulaRelationOperator.GreaterThan,
                    new Formula.Binary(At(Q("Fin", "val"), F.Id("i")), FormulaBinaryOperator.Add, D(1))))))));
    private static Formula CountFormula(string name, string parity) => All("n", N(),
        Equal(At(Local(name), F.Id("n")), At(Q("Fintype", "card"),
            Subtype("p", Partition(F.Id("n")), At(Q(parity), At(Local("excedances"), F.Id("p")))))));
    private static Formula ClaimFormula() => Equal(Typed(Local("claim"), Q("Prop")),
        All("n", N(), new Formula.TypeArrow(Rel(D(1,2), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
            Rel(At(Local("evenCount"), F.Id("n")), FormulaRelationOperator.GreaterThan, At(Local("oddCount"), F.Id("n"))))));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Partition(Formula n) => At(Q("Nat", "Partition"), n);
    private static Formula Local(string name) => Q("D5", "S3", "Combinatorics", "Partitions", "AndrewsHopkinsExcedanceParityRefutation", name);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts) { if (items.Count > 0) items.Add(Dot); items.Add(F.Id(part)); }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Typed(Formula value, Formula type) => Seq(Open, value, Colon, Sp, type, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp, body);
    private static Formula Subtype(string name, Formula type, Formula predicate) => Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Rel(Formula left, FormulaRelationOperator relation, Formula right) => new Formula.Relation(left, relation, right);
}
