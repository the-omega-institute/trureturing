using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class LongReservoirDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/LongReservoir";
    private static Formula Qualified(params Formula[] names) => Seq(Operatorname, Grp(names));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LongReservoir supplies the width-three bridge max-flow proof.",
        H("LongReservoir"), Blocks(
            Paragraph(Text("Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.")),
            Describe.Lean(DescribeId.Create("gls-longreservoir-base-witness"),
                DeclarationHandle.Create(Owner + ".base_witness"),
                H("base_witness"), StatementSource.FromAuthor(Disp(Statement0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every pair of positive dimension pairs with a < b < 2*a and c < d < 2*c admits rational three-slice matrices attaining the outer cut. A shift pencil with κ=p couples short and long blocks to a cyclic reservoir, and QuantumMaxFlowMinCut.claim_of_hypotheses applies the resulting construction in its strict base case."))),
                DescribeRole.Theorem))));

    private static Formula Statement0() =>
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("BaseWitness"));

}
