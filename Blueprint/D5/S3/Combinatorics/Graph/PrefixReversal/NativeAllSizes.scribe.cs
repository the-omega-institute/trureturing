using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeAllSizesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native state construction closes at the full permutation domain for every size.",
        H("Native Hamilton Cycles at Every Size"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-all-sizes-hamiltonian-cycle"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/PrefixReversal/NativeAllSizes.native_all_sizes_hamiltonian_cycle"),
            H("Three Native Prefix Reversals Admit a Hamilton Cycle"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every natural m at least three, the actual multiplication Cayley graph on Configuration m with the three generators a m, b m and c m has a Hamilton cycle. Configuration m is the permutation type on m plus one labels, so this covers every label count at least four. The four-label and five-label cases use the native base constructions; the six-label case uses the unconditional two-selected-label parent construction. For m at least six, the final frame selects m minus three labels and has a base of exactly three labels. The all-frame strong-state theorem supplies the special Hamilton path and the Hamilton cycles for each actual rotated ordinary child at this same order. Their remaining-b invariant earns the precise supplier edge opened in each child. The independent child partition and native seam assembly then produce a Hamilton cycle on the final parent domain. This final assembly only requires base length at least three; it does not call the state transition that consumes an additional base label. The three-label full-parent-domain isomorphism maps this cycle to the entire permutation Cayley graph. No recursive Hamiltonicity certificate or unproved endpoint state is an assumption of the result, and no literature novelty is asserted."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula m = F.Id("m"), b = F.Id("base"), w = F.Id("walk");
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            Some("base", Call("Configuration", m),
                Some("walk", Call("NativeClosedWalk", m, b),
                    Call("IsHamiltonianCycle", w))))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
