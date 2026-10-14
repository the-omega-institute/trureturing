using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2ParentCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual native F2 witnesses construct a special Hamilton path and all ordinary children, earning an unconditional Hamilton cycle on the full independent parent domain.",
        H("Unconditional Native Two-Label Parent Construction"),
        Blocks(
            Item("native_j2_special_hamilton_path", "The Native Special Child Has a Hamilton Path", PathFormula(),
                "For every m at least five, every two-selected-label supply frame F and every base length at least three, the actual special child has a Hamilton path from R0 to L2. FrameDomain and SpecialDomain are proved equal on configurations. The false-half pieces of one native F2 Hamilton cycle are transported through that identity map, and their exact three cuts are identified with specialCuts. Their literal endpoint pairs R0/R2, L0/L1 and R1/L2 satisfy the E2 boundary law. The native c seam assembler then constructs the path from these particular pieces with full support and remaining-edge permutations. No special-path or target-partition certificate is assumed."),
            Item("native_j2_parent_hamiltonian_cycle", "The Full Parent Has an Unconditional Hamilton Cycle", ParentFormula(),
                "For every m at least five and every two-selected-label supply frame with base length at least three, there is a Hamilton cycle on ParentDomain based at R0. The special path is constructed by the preceding theorem. For each nonzero actual base gap, nativeChildFrame rotates only the base, and the native F2 theorem supplies a genuine Hamilton cycle with its earned remaining-b invariant. The invariant proves the literal ordinary supplier cut, so that same walk yields a SpecifiedOrdinaryCycle. Opening those cuts and connecting all actual child paths uses the independent complete child partition to exhaust ParentDomain. The theorem assumes no previous parent cycle, recursive hstep certificate or unproved endpoint state. Its saved boundary consumer maps the final m=5 parent through fullParentDomainIso to the six-label ambient Cayley graph."))));

    private static Formula PathFormula()
    {
        Formula frame = F.Id("frame"), q = F.Id("q");
        return Framed(Some("q", Call("SpecialWalk", frame, Call("Port", D(0), D(0)),
            Call("Port", D(2), D(1))), Call("IsHamiltonian", q)));
    }

    private static Formula ParentFormula()
    {
        Formula frame = F.Id("frame"), b = F.Id("base"), c = F.Id("cycle");
        return Framed(Some("base", Call("ParentVertex", frame),
            Some("cycle", Call("ParentClosedWalk", frame, b),
                And(Eq(Call("Value", b), Call("rightPort", frame, D(0))),
                    Call("IsHamiltonianCycle", c)))));
    }

    private static Formula Framed(Formula body)
    {
        Formula m = F.Id("m"), frame = F.Id("frame");
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m),
            All("frame", Call("SupplyFrame", m, D(2)),
                Implies(Le(D(3), Call("Length", Call("Base", frame))), body)))));
    }

    private static DocumentBlock Item(string name, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
