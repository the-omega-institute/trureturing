using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2ParentWitnessesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original raw P and outer Q cycles, their literal joint and restored halves, the actual child openings, and the resulting parent are retained as one construction.",
        H("Actual Native Two-Label Suppliers and Their Parent"),
        Blocks(
            Item("native_j2_raw_seed", "Keep the Raw Supplier and All Three Partitions",
                Framed(Nonempty("RawSeedFor", F.Id("m"), F.Id("frame"))),
                "Choose the native F2 witness once. RawSeedFor retains its raw base and closed walk, Hamiltonicity and exact native edge inventory. Its mapped SeedFor retains the same walk through an explicit base equality and heterogeneous walk equality, the six joint pieces and both three-piece halves, their literal ports and simultaneous actual partitions, and all protected-a, remaining-b and selected-c invariants. Both mapped cut groups are explicitly the images of the raw false and true half cuts."),
            Item("native_j2_special_from_raw_seed", "Use This Supplier for the Actual Special Path",
                Framed(WithBase(All("seed", Call("RawSeedFor", F.Id("m"), F.Id("frame")),
                    Nonempty("SpecialPathFor", F.Id("frame"), F.Id("seed"))))),
                "For a supplied RawSeedFor and base length at least three, map its primary false-half pieces to the equal special domain. Their exact cut image is proved equal to specialCuts and their literal E2 port pairs are earned. The special assembler retains the ordered three pieces, the actual Hamilton path R0 to L2, its full support equality and seam-chain equality, and the uncut edge inventory of this same supplier."),
            Item("native_j2_ordinary_from_raw_seed", "Keep the Same Ordinary Supplier Cycle",
                Framed(WithBase(All("gap", Call("BaseGap", F.Id("frame")),
                    Implies(Le(D(1), Call("Index", F.Id("gap"))),
                        All("seed", Call("RawSeedFor", F.Id("m"), Call("nativeChildFrame", F.Id("frame"), F.Id("gap"))),
                            Nonempty("OrdinaryCycleFor", F.Id("frame"), F.Id("gap"), F.Id("seed"))))))),
                "For every nonzero actual base gap and that child's supplied raw seed, the remaining-b invariant proves membership of the literal supplier cut. OrdinaryCycleFor retains the exact SpecifiedOrdinaryCycle and the base equality and walk-copy equality identifying it with the image of this same seed. Its complete joint and both half partitions therefore remain attached to the cycle that is opened."),
            Item("native_j2_parent_with_raw_witnesses", "Keep Every Supplier in Its Actual Parent",
                Framed(WithBase(Nonempty("ParentWitnessFor", F.Id("frame")))),
                "Construct the special and all base-rotated ordinary suppliers from native F2. ParentWitnessFor retains each raw seed and mapped supplier, the actual special path and every ordinary opening, the exact complement-edge inventory after its own supplier cut, and the resulting full parent Hamilton cycle. It retains the literal child-piece inclusions, the R0 base coordinate, full parent support equality and complete closing seam-chain equality."),
            Item("native_j2_old_p_specified_ordinary", "The Final Child Uses the Original Old P Walk",
                Outer(All("P", Call("RawSeedFor", F.Id("m"), F.Id("frame")),
                    Nonempty("OldPCycleFor", F.Id("frame"), F.Id("A"), F.Id("u"), F.Id("P")))),
                "For old P with base A appended by u and A of length at least three, the earned native_p_marked_domain_eq_child identity maps the original old P special domain to the final child of its outer frame. This identity preserves every configuration while retaining the old terminal, base and literal port table inside the saved witness. The old P remaining-b invariant proves the actual final supplier cut. OldPCycleFor records the exact same mapped walk through base and walk-copy equalities; no replacement final-child cycle is selected."),
            Item("native_j2_outer_parent_with_raw_p_q", "The Actual Outer Parent Retains Original P and Outer Q",
                Outer(Nonempty("OuterParentWitnessFor", F.Id("frame"), F.Id("A"), F.Id("u"))),
                "Construct original P and outer Q raw native witnesses and all three actual partitions on each same supplier. Use Q's exact false-half assembly for the special path and P's same mapped cycle for the final child; other children use their retained ordinary suppliers. OuterParentWitnessFor earns an actual Hamilton cycle on the independently defined outer parent and retains the equality attaching its final supplied cycle to the original P witness, every actual opening and complement inventory, literal full support and complete edge chain. Current-parent joint propagation, the next strong StateFor and all-size Hamiltonicity remain subsequent obligations."))));

    private static Formula Framed(Formula body) => Disp(All("m", Call("Nat"),
        Implies(Le(D(5), F.Id("m")), All("frame", Call("SupplyFrame", F.Id("m"), D(2)), body))));
    private static Formula WithBase(Formula body) =>
        Implies(Le(D(3), Call("Length", Call("Base", F.Id("frame")))), body);
    private static Formula Outer(Formula body) => Framed(All("A", Call("LabelList", F.Id("m")),
        All("u", Call("Label", F.Id("m")), Implies(
            And(Eq(Call("Base", F.Id("frame")), Call("Append", F.Id("A"), Call("Singleton", F.Id("u")))),
                Le(D(3), Call("Length", F.Id("A")))), body))));
    private static DocumentBlock Item(string name, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Nonempty(string type, params Formula[] args) => Call("Nonempty", Call(type, args));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
