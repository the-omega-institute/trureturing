using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class ZeroSlopeCombinationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero drift slopes have a codimension-one zero-slope combination space.",
        H("Zero-Slope Combinations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-slope-combinations-finrank-add-one"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/ZeroSlopeCombinations."
                    + "zero_slope_combinations_finrank_add_one"),
                H("Zero-slope combinations have codimension one"),
                StatementSource.FromAuthor(ZeroSlopeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let s be a nonzero real linear functional on the coefficient space "
                        + "of a finite cycle of length ell. Its kernel is the space of linear "
                        + "combinations whose total drift slope is zero. The dimension of this "
                        + "kernel plus one is ell.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. The exact codimension-one "
                        + "result Module.Dual.finrank_ker_add_one_of_ne_zero was found and is "
                        + "applied directly; Module.finrank_fin_fun identifies the ambient "
                        + "dimension with the cycle length.")),
                    Paragraph(Text(
                        "This closes only the source atom's claim that zero-slope combinations "
                        + "on the cycle form an ell-minus-one-dimensional space. The neighboring "
                        + "closed forms, compatibility identity, and erratum are not claimed here."))),
                DescribeRole.Theorem))));

    private static Formula ZeroSlopeFormula()
    {
        Formula ell = F.Id("ell");
        Formula slope = F.Id("s");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula coefficients = Seq(reals, Caret, Grp(ell));
        Formula dual = Seq(Operatorname, Grp(F.Id("Dual")), Open, coefficients, Close);
        Formula kernelDimension = Seq(
            Operatorname, Grp(F.Id("dim")), Underscore, Grp(reals),
            Open, Operatorname, Grp(F.Id("ker")), Open, slope, Close, Close);

        return Disp(Seq(
            Forall, Sp, ell, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Forall, Sp, slope, Colon, Sp, dual, Comma, Esc,
            slope, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            kernelDimension, Sp, Plus, Sp, D(1), Sp, Eq, Sp, ell, Dot));
    }
}
