using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class EnergyBoundarySelectionLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit five-adic boundary map carries lattice energy to twice its residue.",
        H("Energy-Boundary Selection Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("energy-boundary-selection-law"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw."
                        + "energy_boundary_selection_law"),
                H("Boundary type is selected by lattice energy modulo five"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Colon, Sp,
                    Mathbb, Grp(F.Id("Z")), Caret, Grp(D(6)), Comma, Sp,
                    Call("boundaryQuadratic", Call("boundaryProjection", F.Id("x"))),
                    Sp, Eq, Sp, D(2), Cdot, Sp,
                    Call("latticeEnergyModFive", F.Id("x")), Comma, Sp,
                    Operatorname, Grp(F.Id("in")), Sp, Call("ZMod", D(5))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The integral carrier is the lattice Lambda^2 A4 in its chosen "
                            + "six-vector basis. The imported integralGramMatrix is the "
                            + "source's displayed six-by-six Gram matrix, so every integral "
                            + "coordinate vector is an element of that lattice rather than "
                            + "a surrogate finite carrier.")),
                    Paragraph(Text(
                        "The boundaryProjectionMatrix is the displayed three-by-six matrix "
                            + "over ZMod 5, and boundaryProjection first reduces the integral "
                            + "coordinates modulo five before multiplying by that matrix. "
                            + "The boundary quadratic form uses the displayed symmetric "
                            + "three-by-three matrix.")),
                    Paragraph(Text(
                        "Expanding both matrix products proves the nontrivial polynomial "
                            + "identity for all six integral coordinates. Thus the boundary "
                            + "quadratic value equals twice the Gram energy in ZMod 5."))),
                DescribeRole.Theorem))));
}
