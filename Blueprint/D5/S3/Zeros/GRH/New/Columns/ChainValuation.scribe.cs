using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Columns;

internal sealed class ChainValuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chain Valuation", H("Chain Valuation"),
        Blocks(
            Paragraph(Text("Determinant theta class sum: twist-free expansion and norm relation on adding a place. Short integral algebraic forms span; ramified columns have nearly full dimension. Record of a good finite datum: support, integrality, invariance, shape at N. The chain as a sum over classes; good data are standard at p. Valuation gains of single lifts add along the chain with modified data.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Columns/ChainValuation.gaugeLe_chain"),
                H("gaugeLe_chain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Ψ be good, twist primes prime to p, and t_j operators commuting with the levels on the data. If each modified datum multiplies gauges by at most p^{r_j} from d_j to d_{j+1}, the modified chain sends columns integral at d_0 to forms of gauge ≤ p^{∑r_j} at d_m.")))))));
}
