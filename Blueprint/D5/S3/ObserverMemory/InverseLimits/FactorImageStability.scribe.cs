using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class FactorImageStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective semiconjugacies preserve finite iterate-image bounds and stabilization.",
        H("Factor Image Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("surjective-semiconjugacies-preserve-iterate-images"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/FactorImageStability."
                    + "surjective_semiconj_iterate_ranges"),
                H("Factor maps preserve iterate images and stabilization"),
                StatementSource.FromAuthor(FactorImageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let quotientMap be a surjection from a finite source carrier Y onto Z, "
                            + "semiconjugating sourceStep to factorStep. At every time k, its "
                            + "image of the source iterate range is exactly the factor iterate "
                            + "range.")),
                    Paragraph(Text(
                        "Consequently the factor range has at most as many states as the source "
                            + "range. If the source image chain is already stable between k and "
                            + "k+1, applying quotientMap shows that the factor image chain is "
                            + "stable at the same step.")),
                    Paragraph(Text(
                        "This closes theorem/8.6 from qdo-v1: factor coarse-graining does not "
                            + "increase transient image depth. The statement records the iterate "
                            + "image equality, its finite-cardinality consequence, and the "
                            + "stabilization implication.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplied Function.Semiconj.iterate_right, Set.range_comp, "
                            + "Function.Surjective.range_comp, and Set.ncard_image_le. Repository "
                            + "and pinned-source searches found no full theorem. Loogle returned "
                            + "zero hits; LeanSearch's API returned HTTP 404 and supplied no "
                            + "search conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
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

    private static Formula Iterate(Formula function, Formula time) =>
        Seq(function, Caret, Grp(time));

    private static Formula Range(Formula function, Formula time) =>
        Apply(Seq(Operatorname, Grp(F.Id("range"))), Iterate(function, time));

    private static Formula Ncard(Formula set) =>
        Apply(Seq(Operatorname, Grp(F.Id("ncard"))), set);

    private static Formula FactorImageFormula()
    {
        Formula sourceCarrier = F.Id("Y");
        Formula factorCarrier = F.Id("Z");
        Formula sourceStep = F.Id("sourceStep");
        Formula factorStep = F.Id("factorStep");
        Formula quotientMap = F.Id("quotientMap");
        Formula time = F.Id("k");
        Formula nextTime = Seq(time, Sp, Plus, Sp, D(1));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula sourceRange = Range(sourceStep, time);
        Formula factorRange = Range(factorStep, time);
        Formula nextSourceRange = Range(sourceStep, nextTime);
        Formula nextFactorRange = Range(factorStep, nextTime);
        Formula finiteSource = Seq(
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, sourceCarrier, CloseBracket);
        Formula surjective = Apply(
            Seq(Operatorname, Grp(F.Id("Surjective"))), quotientMap);
        Formula semiconj = Apply(
            Seq(Operatorname, Grp(F.Id("Semiconj"))),
            quotientMap,
            sourceStep,
            factorStep);
        Formula image = Apply(
            Seq(Operatorname, Grp(F.Id("image"))), quotientMap, sourceRange);

        return Disp(Seq(
            Forall, Sp, sourceCarrier, Comma, Sp, factorCarrier, Comma, Sp,
            finiteSource, Comma, Esc,
            sourceStep, Colon, Sp, sourceCarrier, Sp, To, Sp, sourceCarrier, Comma, Esc,
            factorStep, Colon, Sp, factorCarrier, Sp, To, Sp, factorCarrier, Comma, Esc,
            quotientMap, Colon, Sp, sourceCarrier, Sp, To, Sp, factorCarrier, Comma, Esc,
            surjective, Sp, Land, Sp, semiconj, Sp, Rightarrow, Sp,
            Forall, Sp, time, InMacro, Sp, natural, Comma, Esc,
            image, Sp, Eq, Sp, factorRange, Sp, Land, Esc,
            Ncard(factorRange), Sp, Leq, Sp, Ncard(sourceRange), Sp, Land, Esc,
            Open, sourceRange, Sp, Eq, Sp, nextSourceRange, Sp, Rightarrow, Sp,
            factorRange, Sp, Eq, Sp, nextFactorRange, Close, Dot));
    }
}
