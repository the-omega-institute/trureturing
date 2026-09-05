using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class GoldenExponentialPronyCoordinateDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The split golden sampling atom is a nonvanishing complex character: "
            + "addition of lifted displacements becomes multiplication of Prony nodes, "
            + "natural translation becomes powers, and radius records the real displacement.",
        H("Golden Exponential Prony Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-exponential-coordinate-is-the-sampling-atom"),
                DeclarationHandle.Create(
                    Prefix + "golden_exponential_prony_coordinate_eq_sampling_atom"),
                H("The complex coordinate equals the existing golden sampling atom"),
                StatementSource.FromAuthor(SamplingAtomFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Packaging a complex displacement by its real and imaginary parts reproduces the repository's existing radial-phase golden sampling atom exactly.")),
                    Paragraph(Text(
                        "This theorem prevents a second sampling convention and fixes the sign of both radial damping and phase rotation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-exponential-coordinate-additive-character"),
                DeclarationHandle.Create(
                    Prefix + "golden_exponential_prony_coordinate_add"),
                H("Lifted addition becomes multiplication of Prony nodes"),
                StatementSource.FromAuthor(AddFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The golden exponential coordinate is an additive-to-multiplicative character on the lifted complex displacement plane.")),
                    Paragraph(Text(
                        "Consequently, independent shifts compose without introducing a second transport law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-exponential-coordinate-natural-time-powers"),
                DeclarationHandle.Create(
                    Prefix + "golden_exponential_prony_coordinate_nat_mul"),
                H("Natural translation depth becomes ordinary powers"),
                StatementSource.FromAuthor(NatMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Sampling a lifted displacement after a natural number of equal steps gives the corresponding ordinary power of the one-step node.")),
                    Paragraph(Text(
                        "This is the exact time-character law required by finite Prony and Vandermonde reconstruction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-exponential-coordinate-radius-and-alias-boundary"),
                DeclarationHandle.Create(
                    Prefix + "golden_exponential_prony_coordinate_eq_implies_re_eq"),
                H("Node equality preserves radial displacement"),
                StatementSource.FromAuthor(ReInjectiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equal golden exponential nodes have equal real coordinates because their norms are injective real exponentials of the radial displacement.")),
                    Paragraph(Text(
                        "Any unresolved collision is therefore purely vertical phase aliasing. No global imaginary-direction injectivity is claimed."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula SamplingAtomFormula()
    {
        Formula z = F.Id("z");
        return Disp(Seq(
            Forall, Sp, z, Comma, Sp,
            Call("goldenExponentialPronyCoordinate", z), Sp, Eq, Sp,
            Call("goldenSamplingAtom", Call("im", z), Call("re", z)), Dot));
    }

    private static Formula AddFormula()
    {
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        return Disp(Seq(
            Forall, Sp, z, Comma, Sp, Forall, Sp, w, Comma, Sp,
            Call("goldenExponentialPronyCoordinate", Seq(z, Sp, Plus, Sp, w)), Sp, Eq, Sp,
            Call("goldenExponentialPronyCoordinate", z), Sp, Cdot, Sp,
            Call("goldenExponentialPronyCoordinate", w), Dot));
    }

    private static Formula NatMulFormula()
    {
        Formula t = F.Id("t");
        Formula z = F.Id("z");
        return Disp(Seq(
            Forall, Sp, t, Comma, Sp, Forall, Sp, z, Comma, Sp,
            Call("goldenExponentialPronyCoordinate", Seq(t, Sp, Cdot, Sp, z)), Sp, Eq, Sp,
            Call("goldenExponentialPronyCoordinate", z), Caret, Grp(t), Dot));
    }

    private static Formula ReInjectiveFormula()
    {
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        return Disp(Seq(
            Forall, Sp, z, Comma, Sp, Forall, Sp, w, Comma, Sp,
            Call("goldenExponentialPronyCoordinate", z), Sp, Eq, Sp,
            Call("goldenExponentialPronyCoordinate", w), Sp, Rightarrow, Sp,
            Call("re", z), Sp, Eq, Sp, Call("re", w), Dot));
    }

}
