using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class RamifiedFiveDissectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five energy residues plus one nonzero isotropic zero-fiber state form six readouts.",
        H("Ramified Five-Dissection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ramified-five-dissection"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/RamifiedFiveDissection."
                        + "ramified_five_dissection"),
                H("Five ordinary residues and one zero-fiber residual form six states"),
                StatementSource.FromAuthor(DissectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the canonical six-coordinate integral lattice from "
                            + "ExactDualLatticeFormula. Integer reduction is coordinatewise "
                            + "reduction into ZMod five. The boundary reduction and quadratic "
                            + "form are built from the explicit source matrices R-five and H; "
                            + "the energy uses the imported canonical Gram matrix.")),
                    Paragraph(Text(
                        "The readout pairs the ordinary energy residue with the Boolean decision "
                            + "that the boundary vector is nonzero and isotropic. Its exact image "
                            + "is the five false-bit residue states together with the single "
                            + "zero-residue true-bit state. The final conjunct records that this "
                            + "concrete image has cardinality six.")),
                    Paragraph(Text(
                        "The selection identity is proved from the two displayed matrices. The "
                            + "five ordinary states and the extra residual state are realized by "
                            + "explicit reduced lattice vectors; coordinatewise integer lifts "
                            + "then prove the same exact image on the source lattice carrier.")),
                    Paragraph(Text(
                        "Repository searches found the canonical Gram data but no boundary or "
                            + "six-state theorem. Pinned Mathlib contributes the matrix-vector, "
                            + "finite range, and modular arithmetic infrastructure only."))),
                DescribeRole.Theorem))));

    private static Formula DissectionFormula()
    {
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula latticeIndex = Call("Fin", D(6));
        Formula latticeCarrier = Seq(latticeIndex, Sp, To, Sp, integer);
        Formula residue = Call("ZMod", D(5));
        Formula x = F.Id("x");
        Formula r = F.Id("r");
        Formula reduction = Call("integerReduction", x);
        Formula boundary = Call("boundaryReduction", reduction);
        Formula quadratic = Call("boundaryQuadratic", boundary);
        Formula energy = Call("energyResidue", reduction);
        Formula residual = Call("decide", Seq(
            boundary, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            quadratic, Sp, Eq, Sp, D(0)));
        Formula readout = Seq(Open, energy, Comma, Sp, residual, Close);
        Formula integerReadout = Seq(
            Open, x, Colon, Sp, latticeCarrier, Sp, Mapsto, Sp, readout, Close);
        Formula readoutRange = Call("range", integerReadout);
        Formula ordinaryRange = Call("range", Seq(
            Open, r, Colon, Sp, residue, Sp, Mapsto, Sp,
            Open, r, Comma, Sp, F.Id("false"), Close, Close));
        Formula residualState = Seq(
            OpenBrace, Open, D(0), Comma, Sp, F.Id("true"), Close, CloseBrace);
        Formula sixStates = Call("union", ordinaryRange, residualState);

        return Disp(new Formula.Aligned([
            Seq(
                Open, Forall, Sp, x, Colon, Sp, latticeCarrier, Comma, Sp,
                Call("boundaryQuadratic", Call("boundaryReduction", Call("integerReduction", x))),
                Sp, Eq, Sp, D(2), Sp,
                Call("energyResidue", Call("integerReduction", x)), Close, Sp, Land),
            Seq(Grp(), readoutRange, Sp, Eq, Sp, sixStates, Sp, Land),
            Seq(Grp(), Call("ncard", readoutRange), Sp, Eq, Sp, D(6), Dot),
        ]));
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
