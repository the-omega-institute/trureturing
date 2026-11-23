using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class SparseCyclicMajorantsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/SparseCyclicMajorants";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite Fourier support bounds the mean of a nonnegative cyclic majorant.",
        H("Sparse Fourier Support of a Nonnegative Cyclic Majorant"),
        Blocks(
            Paragraph(Text(
                "Let q be a positive integer and K a nonnegative real function on the cyclic group "
                + "of order q. Let S be a set of frequencies containing every nonzero coefficient "
                + "of the unnormalized discrete Fourier transform of K. Write M for the sum of "
                + "K over the group and A(k,x) for the real part of the standard character "
                + "evaluated at −xk modulo q.")),
            Paragraph(Text("Let R be any subset on which K is at least one.")),
            Describe.Lean(
                DescribeId.Create("sparse-dft-majorant-gap"),
                DeclarationHandle.Create(Owner + ".sparse_dft_majorant_gap"),
                H("A lower bound with a correction from the set being majorized"),
                StatementSource.FromAuthor(Gap()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fourier inversion at zero expresses the right side as the double sum over "
                    + "S and the entire cyclic "
                    + "group with terms K(x) times (1−A(k,x)). Each term is nonnegative. Restrict to "
                    + "R and use K(x) at least one."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the equality criterion assume K(0) is positive. Write SubgroupForm(K,S) "
                + "for the existence of an additive subgroup H such that K equals K(0) on H "
                + "and zero outside H, with S equal to the annihilator of H. The annihilator "
                + "consists of the frequencies whose characters are one on H.")),
            Describe.Lean(
                DescribeId.Create("sparse-dft-floor-eq-iff"),
                DeclarationHandle.Create(Owner + ".sparse_dft_floor_eq_iff"),
                H("Equality in the mean bound"),
                StatementSource.FromAuthor(Equality()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under equality, all phase terms with positive K(x) vanish. The support of K "
                    + "is therefore contained in the subgroup where every selected character is "
                    + "one. Inversion makes K constant on that subgroup. Every frequency in its "
                    + "annihilator has the same positive coefficient M and thus belongs to S. "
                    + "Conversely the phase terms vanish for a scaled subgroup indicator with "
                    + "its annihilator as the frequency set."))),
                DescribeRole.Theorem))));

    private static Formula Gap()
    {
        var k = F.Id("k");
        var x = F.Id("x");
        var term = Seq(Open, D(1), Minus, Call("A", k, x), Close);
        var sum = Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, F.Id("S"))), Sp,
            new Formula.Subscript(Sum, Seq(x, Sp, InMacro, Sp, F.Id("R"))), Sp, term);
        return Disp(Seq(sum, Sp, Leq, Sp, Left(), Minus, Right()));
    }

    private static Formula Equality() =>
        Disp(Seq(Left(), Sp, Eq, Sp, Right(), Sp, Iff, Sp, Call("SubgroupForm", F.Id("K"), F.Id("S"))));

    private static Formula Left() => Multiply(new Formula.Absolute(F.Id("S")), F.Id("M"));

    private static Formula Right() => Multiply(F.Id("q"), Call("K", D(0)));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
