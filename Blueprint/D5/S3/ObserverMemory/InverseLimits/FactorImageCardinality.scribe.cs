using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class FactorImageCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A surjective factor map carries every finite iterate image onto the factor image.",
        H("Factor Image Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factor-iterate-image-equality-and-cardinality-bound"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/FactorImageCardinality."
                        + "factor_iterate_range_image_and_cardinality"),
                H("Factor iterate images have no larger cardinality"),
                StatementSource.FromAuthor(FactorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y and Z be finite carriers, tau and sigma self-maps, and phi a "
                            + "surjective map with phi semiconjugating tau to sigma. For every "
                            + "iterate k, phi maps the range of tau^k exactly onto the range "
                            + "of sigma^k. The finite cardinality of the factor image is "
                            + "therefore at most that of the original image.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Function.Semiconj.iterate_right for the "
                            + "iterated semiconjugacy and Set.ncard_image_le for the exact "
                            + "finite image bound. The proof uses the surjectivity hypothesis "
                            + "only for the reverse inclusion in the image equality.")),
                    Paragraph(Text(
                        "This closes the image-equality and cardinality clauses of qdo-v1 "
                            + "theorem 8.6. It does not claim the separate assertion that a "
                            + "stable source image chain forces a stable factor chain."))),
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

    private static Formula Iterate(Formula map, Formula exponent) =>
        Seq(map, Caret, Grp(exponent));

    private static Formula Range(Formula map, Formula exponent) =>
        Apply(Seq(Operatorname, Grp(F.Id("range"))), Iterate(map, exponent));

    private static Formula Ncard(Formula set) =>
        Apply(Seq(Operatorname, Grp(F.Id("ncard"))), set);

    private static Formula FactorFormula()
    {
        Formula y = F.Id("Y");
        Formula z = F.Id("Z");
        Formula phi = F.Id("phi");
        Formula tau = F.Id("tau");
        Formula sigma = F.Id("sigma");
        Formula k = F.Id("k");
        Formula tauRange = Range(tau, k);
        Formula sigmaRange = Range(sigma, k);
        return Disp(Seq(
            Forall, Sp, y, Comma, Sp, z, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, y, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, z, CloseBracket, Comma, Esc,
            phi, Colon, Sp, y, Sp, To, Sp, z, Comma, Sp,
            tau, Colon, Sp, y, Sp, To, Sp, y, Comma, Sp,
            sigma, Colon, Sp, z, Sp, To, Sp, z, Comma, Sp,
            Call("Surjective", phi), Sp, Land, Sp,
            Call("Semiconj", phi, tau, sigma), Sp, Rightarrow, Esc,
            Forall, Sp, k, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Apply(Seq(Operatorname, Grp(F.Id("image"))), phi, tauRange), Sp,
            Eq, Sp, sigmaRange, Sp, Land, Sp,
            Ncard(sigmaRange), Sp, Leq, Sp, Ncard(tauRange), Dot));
    }
}
