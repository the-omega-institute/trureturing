using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class RamifiedFiveBoundarySelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden discriminant selects five as the unique ramified prime and lattice boundary modulus.",
        H("Ramified-Five Boundary Selection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ramified-five-boundary-selection"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/RamifiedFiveBoundarySelection."
                        + "ramified_five_boundary_selection"),
                H("The unique ramified prime is the canonical boundary modulus"),
                StatementSource.FromAuthor(SelectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first row computes the discriminant of the canonical golden polynomial "
                            + "from its integer coefficients. The second row exhibits five as the "
                            + "square of the ramifying golden integer in the canonical GoldenInt carrier.")),
                    Paragraph(Text(
                        "For every rational prime, the quadratic character modulo five vanishes "
                            + "exactly at five. This gives the unique finite ramified location without "
                            + "restricting the prime carrier to a finite list or to odd primes.")),
                    Paragraph(Text(
                        "The last row uses the source's canonical six-coordinate lattice, explicit "
                            + "three-dimensional boundary projection, boundary quadratic form, and "
                            + "integral Gram energy. It states the exact mod-five selection law on every "
                            + "integral lattice vector.")),
                    Paragraph(Text(
                        "Repository search found the frozen golden discriminant, ramified-square, and "
                            + "energy-boundary laws, but no theorem combining them with uniqueness of the "
                            + "ramified prime. Pinned Mathlib supplies the Legendre zero criterion and "
                            + "modular divisibility bridge used for that uniqueness step."))),
                DescribeRole.Theorem))));

    private static Formula SelectionFormula()
    {
        Formula prime = F.Id("p");
        Formula x = F.Id("x");
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula latticeCarrier = Seq(Call("Fin", D(6)), Sp, To, Sp, integer);
        Formula ramifyingInteger = Seq(Open, Minus, D(1), Sp, Plus, Sp, D(2), Varphi, Close);

        return Disp(new Formula.Aligned([
            Seq(
                new Formula.Power(Seq(Open, Minus, D(1), Close), D(2)), Sp,
                Minus, Sp, D(4), Times, D(1), Times, Seq(Open, Minus, D(1), Close),
                Sp, Eq, Sp, D(5), Sp, Land),
            Seq(
                Grp(), Call("cast", D(5), F.Id("GoldenInt")), Sp, Eq, Sp,
                new Formula.Power(ramifyingInteger, D(2)), Sp, Land),
            Seq(
                Grp(), Open, Forall, Sp, prime, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Call("Prime", prime), Sp, Rightarrow, Sp, Open,
                Call("legendreSym", D(5), prime), Sp, Eq, Sp, D(0), Sp,
                Leftrightarrow, Sp, prime, Sp, Eq, Sp, D(5), Close, Close, Sp, Land),
            Seq(
                Grp(), Forall, Sp, x, Colon, Sp, latticeCarrier, Comma, Sp,
                Call("boundaryQuadratic", Call("boundaryProjection", x)), Sp, Eq, Sp,
                D(2), Cdot, Sp, Call("latticeEnergyModFive", x), Comma, Sp,
                Operatorname, Grp(F.Id("in")), Sp, Call("ZMod", D(5)), Dot),
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
