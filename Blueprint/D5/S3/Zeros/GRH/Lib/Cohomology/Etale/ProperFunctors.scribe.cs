using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class ProperFunctorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper Functors", H("Proper Functors"),
        Blocks(
            Paragraph(Text("Proper functors: fibre products, base change, dense images, cover by the space of places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/ProperFunctors.isCohomContinuous"),
                H("isCohomContinuous"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A functor of points Z that is proper over D in the sense of IsProperOver has the continuity property IsCohomContinuous for filtered limits, with coefficients in locally constant Λ-valued functions.")))))));
}
