using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate;

internal sealed class GenericFibreTestsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic Fibre Tests", H("Generic Fibre Tests"),
        Blocks(
            Paragraph(Text("Relative ring B_dR+/ξ² on p-adic tests as square-zero extension of the generic fibre.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GenericFibreTests.exact_mulMu_proj"),
                H("exact_mulMu_proj"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a p-adic test with ring R, K = R[1/p] and B = W(R^♭)[1/p]/(ker θ)², the sequence 0 → K → B → K → 0 is exact, with π induced by θ and ι(θ(b)) = μb.")))))));
}
