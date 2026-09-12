using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenClockWindowCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenClockWindowCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "A sharp interval of real cut offsets preserves every golden clock contraction. "
                + "The classification concerns the entire closed internal window.",
            H("Sharp Golden Window Criterion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-clock-sharp-cut"),
                    DeclarationHandle.Create(Prefix + "sharp_offset_interval"),
                    H("All-resolution invariance has an exact offset range"),
                    StatementSource.FromAuthor(CriterionFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Assume 0<=rho<=1. W(rho) is the closed real interval "
                                + "[-rho,1-rho], d(L)=(-alpha)^(L+2), "
                                + "lower=(1-alpha)/2 and upper=(1+alpha)/2. "
                                + "AllResolutionsPreserve(rho) means d(L)*W(rho) is "
                                + "contained in W(rho) for every natural L. "
                                + "Between(lower,rho,upper) includes both endpoints.")),
                        Paragraph(Text(
                            "The positive scale alpha^2 preserves every normalized "
                                + "window containing zero. The negative scale -alpha^3 "
                                + "imposes the two endpoint inequalities. A two-step "
                                + "induction then covers every L. Outside the stated "
                                + "range, resolution one already fails.")),
                        Paragraph(Text(
                            "This is an exact closed-window theorem. It does not replace "
                                + "a half-open integer-orbit assertion, does not suppress "
                                + "seam cases, and does not select one intrinsically "
                                + "privileged origin. The centered and canonical sections "
                                + "have separate, direct floor proofs."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula CriterionFormula() => Disp(Call("Iff",
        Call("AllResolutionsPreserve", F.Id("rho")),
        Call("Between", F.Id("lower"), F.Id("rho"), F.Id("upper"))));
}
