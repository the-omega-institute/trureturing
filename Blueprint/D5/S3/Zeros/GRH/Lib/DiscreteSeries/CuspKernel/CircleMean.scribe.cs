using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.CuspKernel;

internal sealed class CircleMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle Mean", H("Circle Mean"),
        Blocks(
            Paragraph(Text("Cauchy-Schwarz, Fubini along measure-preserving maps, convolution; integrable minimal idempotent definition. Integrable idempotent kernel kills bounded continuous functions invariant under the unipotent radical.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/CircleMean.le_of_halving"),
                H("le_of_halving"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Maximum principle: let f be a real function bounded above and c ≥ 0. If for every upper bound M ≥ 0 of f each value is ≤ M/2 or ≤ c, then f ≤ c.")))))));
}
