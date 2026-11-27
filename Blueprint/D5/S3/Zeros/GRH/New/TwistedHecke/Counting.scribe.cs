using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.TwistedHecke;

internal sealed class CountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting", H("Counting"),
        Blocks(
            Paragraph(Text("Flag count; amplification bounds dimension of conditioned forms by flags times lattice points. Parahoric index times dim TwistingData.excessCond is at most (1+κ)m^N; size conditions. Forms deep in all frames are rare: their mean depth is small.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/Counting.sum_finrank_deepForms_le"),
                H("sum_finrank_deepForms_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let K have characteristic p and assume HeckeSizes. Then for every M, ∑_{d<M} dim V_d ≤ (1 + z)·m^N, where V_d = TwistingData.deepForms n r d and m is the number of monomials of degree n in k variables.")))))));
}
