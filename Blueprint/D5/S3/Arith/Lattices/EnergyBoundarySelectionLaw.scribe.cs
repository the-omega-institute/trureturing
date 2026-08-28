using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class EnergyBoundarySelectionLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit five-adic boundary map preserves twice the six-dimensional lattice energy modulo five.",
        H("Energy-Boundary Selection Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("energy-boundary-selection-law"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw."
                        + "energy_boundary_selection_law"),
                H("Boundary quadratic value equals twice the lattice energy modulo five"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The variable x ranges over the integral coordinate vectors in the chosen "
                            + "six-element basis of Lambda^2 A4. The imported lattice family owns "
                            + "this coordinate index and the displayed integral Gram matrix.")),
                    Paragraph(Text(
                        "The boundary map multiplies the reduction of x modulo five by the source "
                            + "three-by-six matrix R_5. The boundary quadratic form uses the source "
                            + "three-by-three symmetric matrix H, while the lattice energy uses the "
                            + "imported Gram matrix G.")),
                    Paragraph(Text(
                        "Direct exact matrix normalization over ZMod 5 proves that the boundary "
                            + "quadratic value is twice the reduced Gram energy for every integral "
                            + "lattice coordinate vector."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x");
        Formula latticeIndex = Call("Fin", D(6));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula latticeCoordinates = new Formula.TypeArrow(latticeIndex, integers);
        Formula boundaryValue = Call(
            "boundaryQuadraticForm",
            Call("boundaryMap", x));
        Formula latticeEnergy = Call("latticeEnergyModFive", x);

        return Disp(Seq(
            Forall, Sp, x, Colon, Sp, latticeCoordinates, Comma, Sp,
            boundaryValue, Sp, Eq, Sp, D(2), Sp, latticeEnergy, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
