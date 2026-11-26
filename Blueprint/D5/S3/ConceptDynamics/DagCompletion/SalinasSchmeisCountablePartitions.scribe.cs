using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class SalinasSchmeisCountablePartitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/salinasschmeis2026omega");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cofinal partitions of the naturals and inherited partitions of two poset extensions.",
        H("Countable cofinal partitions and their induced extensions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residue-partition"), DeclarationHandle.Create(Prefix + "residuePartition"),
                H("Residue classes for a positive modulus"), StatementSource.FromAuthor(Disp(ResidueFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The part indexed by i consists of i + m k for k in the naturals, where i < m "
                    + "and m is positive. Euclidean division recovers both the index i and the "
                    + "quotient k from a point of the part. For each index the range is infinite "
                    + "and therefore cofinal in the naturals. Modulus one gives the whole set of "
                    + "naturals as a single part."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-adic-partition"), DeclarationHandle.Create(Prefix + "twoAdicPartition"),
                H("Parts indexed by the exponent of two"), StatementSource.FromAuthor(Disp(Call("IsCofinalNatPartition", F.Id("twoAdicPart")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The part indexed by i is the range of k mapped to 2^i (2 k + 1) - 1. "
                    + "The argument of subtraction is positive. Factor the successor of a natural "
                    + "into a power of two and an odd factor. Its exponent is determined by the "
                    + "factorization and gives the unique part. For each index the range is infinite "
                    + "and cofinal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countable-partition"), DeclarationHandle.Create(Prefix + "countablePartition"),
                H("A cofinal partition for each nonempty countable index type"), StatementSource.FromAuthor(Disp(CountableFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Transport the residue parts along an equivalence with a finite index type "
                    + "when the index is finite. Transport the two-adic parts along an equivalence "
                    + "with the naturals when it is infinite. Every natural belongs to exactly one "
                    + "indexed part and each part is infinite and cofinal. A positive finite "
                    + "cardinality follows from the nonempty hypothesis. An empty index type "
                    + "cannot cover the naturals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordinal-sum-partition"),
                DeclarationHandle.Create(Prefix + "ordinalSumPartition"),
                H("The partition of the ordinal sum U"), StatementSource.FromAuthor(Disp(OrdinalSumFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use the ordinal sum of the original poset P followed by the naturals. "
                        + "The left inclusion preserves and reflects the order of P. Choose a "
                        + "cofinal partition of the right summand indexed by P. The part for p "
                        + "consists of its left image and the right images of the selected naturals.")),
                    Paragraph(Text(
                        "Enumerate the selected infinite subset in its inherited order using "
                        + "Nat.Subtype.orderIsoOfNat. Send zero to the prepended point and each "
                        + "successor to the corresponding element of the increasing enumeration. "
                        + "Strictness at the prepended point and preservation along the tail give "
                        + "an induced copy of the naturals whose range is the literal part."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-ray-partition"),
                DeclarationHandle.Create(Prefix + "maximalRayPartition"),
                H("The partition of the maximal-ray extension V"), StatementSource.FromAuthor(Disp(MaximalRayFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The carrier consists of P and a separate natural ray over each maximal "
                        + "point m. The base keeps its order. A base point is below a ray point "
                        + "exactly when it is below m in P. Rays have their natural order and "
                        + "distinct maximal indices are incomparable. No ray point is below a "
                        + "base point.")),
                    Paragraph(Text(
                        "Take an assignment a sending each p to a maximal point above it. "
                        + "It fixes each maximal point, so its fiber over that point is nonempty. "
                        + "Each assignment fiber is countable as a subtype. Partition the literal "
                        + "ray over m by the assignment fiber and prepend p to the selected tail "
                        + "on the ray over a(p). The ray index and the unique assigned point within "
                        + "that ray determine the part of every ray point. A base point lies "
                        + "only in its own part.")),
                    Paragraph(Text(
                        "The ordinal sum and maximal-ray partitions are the two constructions "
                        + "used in the bounded-height theorem of the revision-2 note by Haobo Ma "
                        + "(ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University of "
                        + "Singapore and ChronoAI Pte Ltd, Singapore). The maximal-ray construction "
                        + "allows countably infinitely many maximal points. These partitions "
                        + "provide admissibility for the comparison targets."))),
                DescribeRole.Theorem))));

    private static Formula ResidueFormula() =>
        All("m", Naturals(), Seq(D(0), Sp, Lt, Sp, F.Id("m"), Sp, Rightarrow, Sp,
            Call("IsCofinalNatPartition", Call("residuePart", F.Id("m")))));

    private static Formula CountableFormula()
    {
        var i = F.Id("I");
        return All("I", TypeU(), WithInstances(
            Exists("S", Seq(i, Sp, To, Sp, Call("Set", Naturals())),
                Call("IsCofinalNatPartition", F.Id("S"))),
            Call("Nonempty", i), Call("Countable", i)));
    }

    private static Formula OrdinalSumFormula()
    {
        var p = F.Id("P");
        var s = F.Id("S");
        return All("P", TypeU(), WithInstances(
            Seq(Call("IsExtension", p, Call("U", p)), Sp, Land, RowBreak,
                Exists("S", Seq(p, Sp, To, Sp, Call("Set", Naturals())),
                    Seq(Call("IsCofinalNatPartition", s), Sp, Land, RowBreak,
                        PartConclusions(Call("ordinalSumPart", s))))),
            Call("PartialOrder", p), Call("Nonempty", p), Call("Countable", p)));
    }

    private static Formula MaximalRayFormula()
    {
        var p = F.Id("P");
        var a = F.Id("a");
        var s = F.Id("S");
        var m = F.Id("m");
        var maxima = Call("MaximalPoints", p);
        var assigned = Seq(OpenBrace, F.Id("p"), Sp, InMacro, Sp, p, Sp, Mid, Sp,
            Equal(Call("a", F.Id("p")), m), CloseBrace);
        var family = Seq(Open, m, Colon, Sp, maxima, Close, Sp, To, Sp,
            assigned, Sp, To, Sp, Call("Set", Naturals()));
        var condition = All("p", p, Seq(F.Id("p"), Sp, Le, Sp, Call("val", Call("a", F.Id("p")))));
        return All("P", TypeU(), WithInstances(
            All("a", Seq(p, Sp, To, Sp, maxima),
                Seq(Open, condition, Close, Sp, Rightarrow, RowBreak,
                    Call("IsExtension", p, Call("MaximalRayExtension", p)), Sp, Land, RowBreak,
                    Exists("S", family, Seq(Open, All("m", maxima,
                        Call("IsCofinalNatPartition", Call("S", m))), Close, Sp, Land, RowBreak,
                        PartConclusions(Call("maximalRayPart", a, s)))))),
            Call("PartialOrder", p), Call("Countable", p)));
    }

    private static Formula PartConclusions(Formula parts) =>
        Seq(Call("IsPartition", Call("range", parts)), Sp, Land, RowBreak,
            All("p", F.Id("P"), Call("IsOmegaChain",
                new Formula.Apply(parts, [F.Id("p")]))));

    private static Formula WithInstances(Formula body, params Formula[] instances)
    {
        var pieces = new List<Formula>();
        foreach (var instance in instances)
            pieces.AddRange([OpenBracket, instance, CloseBracket, Sp]);
        pieces.Add(body);
        return Seq([.. pieces]);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeU() => Seq(F.Id("Type"), Sp, F.Id("u"));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
}
