using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeFourBaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeFourBase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three actual prefix reversals of lengths four, three and two admit a Hamilton cycle on every permutation of four labels.",
        H("Actual Big-3 Hamilton Cycle at Size Four"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-four-hamiltonian-cycle"),
                DeclarationHandle.Create(Prefix + "native_four_hamiltonian_cycle"),
                H("Close the Actual Zero-Star Complement"),
                StatementSource.FromAuthor(CycleFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Apply the existing zeroStar_b_complement_hamiltonian theorem at m=3 "
                        + "to the identity permutation, marked label zero and its deletion residual. "
                        + "The literal complementary word gives a Hamilton path of length 23 "
                        + "from the identity to its actual three-prefix reversal.")),
                    Paragraph(Text(
                        "A Hamilton path has as many support vertices as its finite domain. "
                        + "Thus this independently specified deletion star has 24 elements. "
                        + "The full group on four labels also has 4!=24 elements, so its "
                        + "injective subtype inclusion is bijective. Mapping the actual path "
                        + "therefore visits every permutation exactly once.")),
                    Paragraph(Text(
                        "The removed edge is an actual Cayley edge labeled by the three-prefix "
                        + "reversal. Add it in front of the mapped path to obtain a closed walk "
                        + "whose tail is Hamiltonian and whose length is 24. The standard cycle "
                        + "criterion then proves Hamiltonicity of this concrete closed walk."))),
                DescribeRole.Theorem))));

    private static Formula CycleFormula()
    {
        Formula vertex = F.Id("base"), walk = F.Id("w");
        Formula graph = Call("mulCayley", Call("generatorTriple", D(3)));
        return Disp(Some("base", Call("Configuration", D(3)),
            Some("w", Call("Walk", graph, vertex, vertex), Call("IsHamiltonianCycle", walk))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
}
