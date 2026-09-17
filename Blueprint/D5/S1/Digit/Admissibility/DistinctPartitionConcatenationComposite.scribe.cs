using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class DistinctPartitionConcatenationCompositeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/murthy2005a110454");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The only positive indices without an eligible composite concatenation are one, two, and four.",
        H("Composite Concatenations of Distinct Partition Parts"),
        Blocks(
            Paragraph(Text(
                "OEIS A110454 considers every ordering of the pairwise distinct positive "
                + "parts of a partition and concatenates the ordered parts in base ten. "
                + "Single-part partitions are included, and an eligible value is greater "
                + "than four and composite.")),
            Paragraph(Text(
                "Natural-number digit lists are little-endian. Reversing the list of parts "
                + "before flat-mapping their digit lists therefore makes ofDigits read the "
                + "parts from left to right.")),
            Node("decimalConcatenation", "Decimal concatenation", ConcatenationFormula(),
                "The reversed list of parts is replaced by the base-ten digits of each part, "
                + "then ofDigits evaluates the resulting little-endian digit list.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("C", "All distinct-partition concatenations", CFormula(),
                "Start with the positive integers below or equal to n, take every subset "
                + "whose sum is n, then take every permutation of its sorted list and map "
                + "decimalConcatenation over those permutations. Thus the parts are pairwise "
                + "distinct positive integers summing to n, and every ordering is taken.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("murthy_conjecture", "Murthy's conjecture", ConjectureFormula(),
                "For n=3, the ordered parts two and one give 21. For n at least five, "
                + "the ordered parts n-2 and two give 10(n-2)+2=2(5n-9), an even value "
                + "greater than four. Direct classification at one, two, and four shows "
                + "that their eligible filters are empty.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a110454-distinct-partition-concatenation-zero-indices"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a110454-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula ConcatenationFormula()
    {
        var parts = F.Id("parts");
        var digits = Call("flatMap", Call("digits", D(1, 0)), Call("reverse", parts));
        return Disp(Universal("parts", Lists(),
            Equal(Call("decimalConcatenation", parts), Call("ofDigits", D(1, 0), digits))));
    }

    private static Formula CFormula()
    {
        var n = F.Id("n");
        var parts = F.Id("parts");
        var candidates = Call("filter",
            Call("powerset", Call("erase", Call("range", Add(n, D(1))), D(0))),
            Lambda(parts, Equal(Call("sum", parts, F.Id("id")), n)));
        var orderedValues = Lambda(parts, Call("image", F.Id("decimalConcatenation"),
            Call("toFinset", Call("permutations", Call("sort", parts)))));
        return Disp(Universal("n", Naturals(),
            Equal(Call("C", n), Call("biUnion", candidates, orderedValues))));
    }

    private static Formula ConjectureFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var exceptions = new Formula.SetLiteral([D(1), D(2), D(4)]);
        var eligible = And(Less(D(4), m), new Formula.Not(Call("Prime", m)));
        var existence = Universal("n", Naturals(), Implies(
            LessOrEqual(D(1), n),
            Implies(new Formula.Not(Parenthesized(Member(n, exceptions))),
                Existential("m", Call("C", n), eligible))));
        var exclusion = Universal("n", exceptions, Equal(
            Call("filter", Call("C", n), Lambda(m, eligible)), Emptyset));
        return Disp(And(existence, exclusion));
    }

    private static Formula Naturals() => F.Id("Nat");
    private static Formula Lists() => Call("List", Naturals());
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(variable, Sp, Mapsto, Sp, body));
    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Existential(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
}
