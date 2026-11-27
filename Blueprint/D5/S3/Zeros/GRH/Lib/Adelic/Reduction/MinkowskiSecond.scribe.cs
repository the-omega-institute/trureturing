using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Reduction;

internal sealed class MinkowskiSecondDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minkowski Second", H("Minkowski Second"),
        Blocks(
            Paragraph(Text("A nonzero algebraic integer has a conjugate of modulus at least one. Adelic Blichfeldt count and Minkowski's first theorem with multiplicity. First minimum, height, moderate growth, rapid decay, dilations along an isotropic subspace. Adelic unitary group closed in matrices; definite rational points discrete in finite part. Adelic Minkowski second theorem with crude constant; counting field points in dilated boxes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Reduction/MinkowskiSecond.tsum_prod_le_prod_tsum"),
                H("tsum_prod_le_prod_tsum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For f : α → [0, ∞] and a finite index set n, the sum over all tuples x ∈ α^n of ∏_i f(x_i) is at most (∑_a f(a))^|n|.")))))));
}
