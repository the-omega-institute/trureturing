using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CanonicalImage;

internal sealed class CounterfactualTargetMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fiber-constant target families factor uniquely through the canonical query-profile image.",
        H("Counterfactual Target Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-family-factors-through-canonical-profile-image"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/CanonicalImage/CounterfactualTargetMinimality."
                        + "target_family_factors_through_cf_image"),
                H("Target families factor through the canonical profile image"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The query family sends each model to the set of possible values of each "
                            + "query, and queryProfile collects those answers into one canonical "
                            + "profile. CounterfactualImage is the realized image of this profile, "
                            + "with counterfactualProjection as its canonical map.")),
                    Paragraph(Text(
                        "For every target index, constancy on profile fibers gives a target-valued "
                            + "factor on the image. Surjectivity of the canonical image map makes "
                            + "that factor unique, so all targets in the family descend through the "
                            + "same named image object."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula model = F.Id("M");
        Formula queryIndex = F.Id("J");
        Formula targetIndex = F.Id("K");
        Formula value = F.Id("Value");
        Formula target = F.Id("Target");
        Formula queries = F.Id("queries");
        Formula targets = F.Id("targets");
        Formula index = F.Id("j");
        Formula targetSlot = F.Id("k");
        Formula left = F.Id("m");
        Formula right = F.Id("n");
        Formula factor = F.Id("factor");
        Formula image = Apply("CounterfactualImage", value, queries);
        Formula projection = Apply("counterfactualProjection", value, queries);
        Formula fiberConstancy = Seq(
            Forall, Sp, targetSlot, Comma, Sp, left, Comma, Sp, right, Comma, Sp,
            Apply("queryProfile", value, queries, left), Sp, Eq, Sp,
            Apply("queryProfile", value, queries, right), Sp, Rightarrow, Sp,
            Apply("targets", targetSlot, left), Sp, Eq, Sp, Apply("targets", targetSlot, right));
        Formula factorization = Seq(
            Apply("targets", targetSlot), Sp, Eq, Sp,
            factor, Sp, Circ, Sp, projection);

        return Disp(Seq(
            Forall, Sp, model, Comma, Sp, queryIndex, Comma, Sp, targetIndex, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            value, Colon, Sp, queryIndex, Sp, To, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            target, Colon, Sp, targetIndex, Sp, To, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            queries, Colon, Sp, Forall, Sp, index, Comma, Sp,
            model, Sp, To, Sp,
            Apply("Set", Apply("Value", index)), Comma, Sp,
            targets, Colon, Sp, Forall, Sp, targetSlot, Comma, Sp,
            model, Sp, To, Sp, Apply("Target", targetSlot), Comma, Sp,
            Grp(fiberConstancy), Sp, Rightarrow, Sp,
            Forall, Sp, targetSlot, Comma, Sp,
            Exists, Bang, Sp, factor, Colon, Sp,
            image, Sp, To, Sp, Apply("Target", targetSlot), Comma, Sp,
            factorization, Dot));
    }
}
