using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentSeedConstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The corrected physical current seed",
        H("The corrected physical current seed"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentseedconstruction-seed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeedConstruction.actual_current_seed"),
                H("The physical minus-one seed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every original lattice state and actual tensor target, the field of its minus-one current product plus the half-binomial correction sum equals the physical normal insertion. The source-current upper truncation makes the correction sum genuinely finite. No target vacuum, energy bound or module law is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The singleton at weight one contributes the negative charge pairing divided by two. Each pair of weights one and s has coefficient minus s times choose(1/2,s+1), including the positive one-eighth coefficient when both weights are one. Source partial derivatives retain repeated-colour multiplicities. Finite charge decomposition extends the polynomial identity to the whole original carrier.")),
            Paragraph(Text("The native field exponents use the physical even shifts. The normal insertion retains the negative-current split and the jet exponent plus three.")))));
}
