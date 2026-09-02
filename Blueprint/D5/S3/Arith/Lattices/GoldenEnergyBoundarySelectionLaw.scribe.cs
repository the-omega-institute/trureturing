using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class GoldenEnergyBoundarySelectionLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden prime classes and the unique ramified modulus govern the lattice energy boundary.",
        H("Golden Energy-Boundary Selection Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-energy-boundary-selection-law"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/GoldenEnergyBoundarySelectionLaw."
                        + "golden_energy_boundary_selection_law"),
                H("Golden prime behavior selects the mod-five energy boundary"),
                StatementSource.FromAuthor(SelectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every integral vector in the canonical six-coordinate lattice obeys the "
                            + "energy-boundary equality. Equality of two energy residues therefore "
                            + "forces equality of their boundary quadratic types.")),
                    Paragraph(Text(
                        "For every rational prime, residues one and four modulo five give a split "
                            + "image in the golden integers, while residues two and three give an "
                            + "inert image. These are the plus-or-minus one and plus-or-minus two "
                            + "classes, respectively.")),
                    Paragraph(Text(
                        "Five is the square of the ramifying golden integer and is not prime in the "
                            + "golden integer ring. The quadratic character modulo five vanishes at "
                            + "no other rational prime, exposing the unique finite ramified location "
                            + "used by the lattice boundary.")),
                    Paragraph(Text(
                        "The proof imports the frozen energy, golden-prime classification, and "
                            + "ramified-boundary owners. Pinned Mathlib has the Legendre zero and "
                            + "prime-divisibility facts used by those owners, but no exact theorem "
                            + "combining all five public clauses."))),
                DescribeRole.Theorem))));

    private static Formula SelectionFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula prime = F.Id("p");
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula latticeCarrier = Seq(Call("Fin", D(6)), Sp, To, Sp, integer);
        Formula primeCarrier = Seq(Mathbb, Grp(F.Id("N")));
        Formula energyX = Call("latticeEnergyModFive", x);
        Formula energyY = Call("latticeEnergyModFive", y);
        Formula boundaryX = Call("boundaryQuadratic", Call("boundaryProjection", x));
        Formula boundaryY = Call("boundaryQuadratic", Call("boundaryProjection", y));
        Formula primeInGolden = Call("Prime", Call("cast", prime, F.Id("GoldenInt")));
        Formula fiveInGolden = Call("cast", D(5), F.Id("GoldenInt"));
        Formula primeModFive = Call("mod", prime, D(5));
        Formula ramifyingInteger = Seq(Open, Minus, D(1), Sp, Plus, Sp, D(2), Varphi, Close);

        Formula splitResidues = Seq(
            Open, primeModFive, Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            primeModFive, Sp, Eq, Sp, D(4), Close);
        Formula inertResidues = Seq(
            Open, primeModFive, Sp, Eq, Sp, D(2), Sp, Lor, Sp,
            primeModFive, Sp, Eq, Sp, D(3), Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, x, Colon, Sp, latticeCarrier, Comma, Sp,
                boundaryX, Sp, Eq, Sp, D(2), Cdot, Sp, energyX, Sp, Land),
            Seq(
                Grp(), Forall, Sp, x, Comma, Sp, y, Colon, Sp, latticeCarrier, Comma, Sp,
                energyX, Sp, Eq, Sp, energyY, Sp, Rightarrow, Sp,
                boundaryX, Sp, Eq, Sp, boundaryY, Sp, Land),
            Seq(
                Grp(), Forall, Sp, prime, Sp, InMacro, Sp, primeCarrier, Comma, Sp,
                Call("Prime", prime), Sp, Rightarrow, Sp, Open,
                Open, splitResidues, Sp, Rightarrow, Sp, Neg, primeInGolden, Close,
                Sp, Land, Sp,
                Open, inertResidues, Sp, Rightarrow, Sp, primeInGolden, Close,
                Close, Sp, Land),
            Seq(
                Grp(), Open,
                fiveInGolden, Sp, Eq, Sp, new Formula.Power(ramifyingInteger, D(2)),
                Sp, Land, Sp, Neg, Call("Prime", fiveInGolden), Close, Sp, Land),
            Seq(
                Grp(), Forall, Sp, prime, Sp, InMacro, Sp, primeCarrier, Comma, Sp,
                Call("Prime", prime), Sp, Rightarrow, Sp, Open,
                Call("legendreSym", D(5), prime), Sp, Eq, Sp, D(0), Sp,
                Leftrightarrow, Sp, prime, Sp, Eq, Sp, D(5), Close, Dot),
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
