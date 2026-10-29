using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class MarginalCalculusDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/MarginalCalculus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual tensor-coordinate partial traces compose and respect basis relabeling.", H("Finite Density Marginal Calculus"),
        Blocks(
            Paragraph(Text("Every state is the existing project DensityState. reduceState e rho keeps K and sums the actual matrix diagonal over R, where e identifies K tensor R with the original carrier. The coordinate equivalence is explicit; no entropy values or marginal consistency assumptions are supplied.")),
            Result("composition", "reduceState_compose", "Two actual traces compose", "Tracing R and then T equals tracing T tensor R, after the actual tensor associator. The proof is the finite product-sum identity on matrix entries.",
                Disp(Seq(Call("reduce", F.Id("f"), Call("reduce", F.Id("e"), Rho)), Sp, Eq, Sp, Call("reduce", Call("compose", F.Id("e"), F.Id("f")), Rho)))),
            Result("partition-ssa", "ssa_partition", "SSA after a tensor partition", "For any actual density state and any equivalence to K tensor S tensor R, the receiving SSA theorem applies to the three real marginals. A coordinate sum proves that the retained central register is exactly the iterated partial trace.",
                Disp(Seq(Call("S", F.Id("KSR")), Sp, Plus, Sp, Call("S", F.Id("S")), Sp, Le, Sp, Call("S", F.Id("KS")), Sp, Plus, Sp, Call("S", F.Id("SR"))))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
