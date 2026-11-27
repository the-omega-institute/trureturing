using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar;

internal sealed class LogDerivativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Log Derivative", H("Log Derivative"),
        Blocks(
            Paragraph(Text("Logarithmic derivative on U(J), determinant of congruence, measure-preserving isometries.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/LogDerivative.exists_measurePreserving_equiv"),
                H("exists_measurePreserving_equiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the volume on V satisfy HasGaussianIntegral for q and dim V = n². A linear map f from real n×n matrices to V with q(f y) = Σ y_ab² is the inverse of a measure preserving linear isomorphism from V to real matrices.")))))));
}
