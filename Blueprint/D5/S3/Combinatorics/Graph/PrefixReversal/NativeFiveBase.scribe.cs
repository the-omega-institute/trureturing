using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeFiveBaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeFiveBase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual F2 construction at size five gives a Hamilton cycle on every permutation of five labels.",
        H("Actual Big-3 Hamilton Cycle at Size Five"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-five-domain"),
                DeclarationHandle.Create(Prefix + "native_five_domain"),
                H("Every Permutation Belongs to the Actual F2 Domain"),
                StatementSource.FromAuthor(Disp(All("v", Call("Configuration", D(4)),
                    Call("F2Domain", D(4), F.Id("v"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing native_f2_layer_iff identifies the independently defined "
                    + "F2 union with the layer obtained by erasing labels zero and four. "
                    + "The tuple of every permutation is a reordering of the identity tuple; "
                    + "filtering those two labels leaves a reordering of (1,2,3). Rotate "
                    + "the first label to the head. The remaining pair has two possible orders, "
                    + "giving exactly the reference circle or its reverse. Thus every actual "
                    + "permutation lies in the specified insertion layer and in F2Domain."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-five-hamiltonian-cycle"),
                DeclarationHandle.Create(Prefix + "native_five_hamiltonian_cycle"),
                H("Map the Actual F2 Cycle onto the Full Group"),
                StatementSource.FromAuthor(CycleFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the existing native_f2_hamiltonian_cycle at m=4, whose cycle is "
                    + "constructed from actual contact grafts on the independently specified "
                    + "domain. The proved coverage makes its subtype inclusion bijective. "
                    + "The induced graph inclusion preserves every actual Cayley edge, "
                    + "so mapping this same cycle yields a Hamilton cycle for reversals "
                    + "of lengths five, four and three on all 5!=120 permutations."))),
                DescribeRole.Theorem))));

    private static Formula CycleFormula()
    {
        Formula vertex = F.Id("base"), walk = F.Id("w");
        Formula graph = Call("mulCayley", Call("generatorTriple", D(4)));
        return Disp(Some("base", Call("Configuration", D(4)),
            Some("w", Call("Walk", graph, vertex, vertex), Call("IsHamiltonianCycle", walk))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
