using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RationalTopCycleResiduesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RationalTopCycleResidues";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lift residue cycles to rational top cycles.",
        H("Rational Top Cycle Residues"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-cycle-residues-lift"),
                DeclarationHandle.Create(Module + ".rational_cycle_residues_lift"),
                H("Lift residue cycles to rational top cycles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite ordered matroid, every coefficient function on its bases with values in "
                    + "Q/Z and zero augmented boundary lifts, in all face coordinates at once, to a rational "
                    + "top cycle. Choose rational coefficients on the internally passive bases and combine "
                    + "the integral cycles normalized there. A residue cycle with zero passive coefficients "
                    + "must vanish: the colexicographically largest nonzero basis has an internally active "
                    + "element, and deleting it leaves a single potentially nonzero term of unit sign in the "
                    + "boundary."))),
                DescribeRole.Theorem))));
}
