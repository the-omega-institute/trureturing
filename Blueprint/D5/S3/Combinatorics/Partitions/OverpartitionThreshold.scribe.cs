using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class OverpartitionThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/OverpartitionThreshold.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/bhoria2026missing");
    private static readonly LibraryNoteRef Later =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/aniceto2026identities");
    private static readonly LibraryNoteRef Earlier =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/bal2021stanley");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite identity relates the full threshold statistic on native overpartitions to total and nonoverlined part counts.",
        H("Threshold counts in overpartitions"),
        Blocks(
            Paragraph(Text("Nat denotes the nonnegative integers and Int the integers. An ordinary partition is a multiset of positive integers with sum n. Its support contains its distinct part sizes. Each subset S of that support selects the sizes whose first occurrence is overlined, independently, so every legal marking pattern occurs exactly once. The functions parts and marks below select these two components; indicator is one when its proposition holds and zero otherwise. Every displayed sum and cardinal is finite.")),
            Node("Overpartition", "The native marked carrier", CarrierFormula(),
                "Membership of a pair is shorthand for the dependent pair of an ordinary partition and a subset of its support. There are no additional marking constraints.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("multiplicity", "Multiplicity includes the mark", MultiplicityFormula(),
                "count counts all occurrences in the underlying multiset. Overlining changes none of these counts.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("largest", "Largest part", LargestFormula(),
                "sup is the maximum of the finite support, with value zero on the empty support.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("U", "The full threshold statistic", UFormula(),
                "The interval is closed and begins at one. Missing sizes have multiplicity zero, so they are counted whenever k is positive. For n equal to zero the interval is empty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("T", "Total parts", TFormula(),
                "card(parts(o)) is the number of all occurrences, including marked ones; equivalently it is the sum of their multiplicities over positive sizes.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Earlier)),
            Node("N", "Nonoverlined occurrences", NFormula(),
                "A selected size contributes exactly one overlined occurrence. Subtracting its indicator leaves the actual nonoverlined occurrences.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Earlier)),
            Node("result", "The uniform finite identity", ResultFormula(),
                "For every positive k and every nonnegative n the equality is in Int. The alternating sum is empty for k greater than n. Ordinary Ferrers conjugation preserves the number of distinct sizes, so its reindexing preserves the number of marking subsets and exchanges the largest-part total with the total number of parts. Removing k copies of one positive size gives the threshold recurrence. Toggling the optional mark and removing a nonoverlined occurrence give the frequency recurrence; finite alternating cancellation and the pointwise complementary count yield the displayed equality. The overpartition decomposition, nonoverlined frequency formula and threshold-one and threshold-three ingredients have earlier literature precedents. The cited Question 3 asks for a concise analogue, and the later Conclusion retains that question; neither source asserts this particular formula.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Later, Earlier),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bhoria-eyyunni-santra-2026-overpartition-threshold-identity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("overpartition-threshold-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sum(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, domain)),
            Seq(Open, body, Close));
    private static Formula Kn(Formula body) => All("k", V("Nat"), All("n", V("Nat"), body));
    private static Formula OnO(Formula body) => All("n", V("Nat"), All("o", C("Overpartition", V("n")), body));

    private static Formula CarrierFormula() => All("n", V("Nat"),
        All("p", C("Partition", V("n")), All("S", C("Finset", V("Nat")),
            Iff(In(C("pair", V("p"), V("S")), C("Overpartition", V("n"))),
                C("subset", V("S"), C("support", V("p")))))));
    private static Formula MultiplicityFormula() => OnO(All("r", V("Nat"),
        Eq(C("multiplicity", V("o"), V("r")), C("count", V("r"), C("parts", V("o"))))));
    private static Formula LargestFormula() => OnO(Eq(C("largest", V("o")),
        C("sup", C("support", C("parts", V("o"))))));
    private static Formula UFormula() => Kn(Eq(C("U", V("k"), V("n")),
        Sum("o", C("Overpartition", V("n")),
            Sum("r", C("Icc", D(1), C("largest", V("o"))), C("indicator",
                new Formula.Relation(C("multiplicity", V("o"), V("r")),
                    FormulaRelationOperator.LessThan, V("k")))))));

    private static Formula TFormula() => All("n", V("Nat"), Eq(C("T", V("n")),
        Sum("o", C("Overpartition", V("n")), C("card", C("parts", V("o"))))));
    private static Formula NFormula() => All("j", V("Nat"), All("n", V("Nat"),
        Eq(C("N", V("j"), V("n")), Sum("o", C("Overpartition", V("n")),
            Sub(C("multiplicity", V("o"), V("j")),
                C("indicator", In(V("j"), C("marks", V("o")))))))));
    private static Formula ResultFormula() => Kn(Imp(Le(D(1), V("k")),
        Eq(C("U", V("k"), V("n")), Sub(C("T", V("n")), Mul(D(2),
            Sum("j", C("Icc", V("k"), V("n")), Mul(
                new Formula.Power(Seq(Open, Minus, D(1), Close), Sub(V("j"), V("k"))),
                C("N", V("j"), V("n")))))))));
}
