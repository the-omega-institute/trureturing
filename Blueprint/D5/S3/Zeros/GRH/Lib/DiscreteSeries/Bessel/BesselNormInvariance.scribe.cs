using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bessel;

internal sealed class BesselNormInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel Norm Invariance", H("Bessel Norm Invariance"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bessel/BesselNormInvariance.enorm_besselS_mul"),
                H("enorm_besselS_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Norms of a Bessel function and of its means are invariant under Bessel subgroup.")))))));
}
