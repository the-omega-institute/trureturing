using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ZeroSumGaugeGlobalCompletionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero-sum redistribution of adelic local contributions preserves their global "
            + "additive completion.",
        H("Zero-Sum Gauge Invariance of Global Additive Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-sum-gauge-preserves-global-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion."
                        + "zero_sum_gauge_preserves_global_completion"),
                H("A zero-sum local gauge preserves the global additive completion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The place type is the disjoint sum of finite and infinite places. "
                            + "An adelic local ledger consists of a real contribution at every "
                            + "place together with summability of that family. A zero-sum gauge "
                            + "consists of a shift at every place together with a HasSum witness "
                            + "that its total is zero.")),
                    Paragraph(Text(
                        "The gauge transform replaces each local contribution L_v by L_v + b_v. "
                            + "Mathlib's Summable.tsum_add identifies the transformed total with "
                            + "the sum of the original total and the gauge total; the HasSum "
                            + "witness reduces the latter to zero.")),
                    Paragraph(Text(
                        "This statement formalizes the section-15 additive completion reading. "
                            + "The source separately names an earlier quotient K(C)/G as a "
                            + "structural completion signature, but supplies no map or theorem "
                            + "connecting that quotient to this real-valued sum."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula finitePlaces = Seq(F.Id("V"), Underscore, Grp(F.Id("f")));
        Formula infinitePlaces = Seq(F.Id("V"), Underscore, Grp(Infty));
        Formula places = F.Id("V");
        Formula ledger = F.Id("L");
        Formula gauge = F.Id("b");
        Formula place = F.Id("v");
        Formula local = Seq(F.Id("L"), Underscore, Grp(place));
        Formula shift = Seq(F.Id("b"), Underscore, Grp(place));
        Formula completion = Seq(Delta, Underscore, Grp(F.Id("glob")));
        Formula placeSum = Call("Sum", finitePlaces, infinitePlaces);
        Formula originalSum = Seq(
            Sum, Underscore, Grp(place, InMacro, Sp, places), Sp, local);
        Formula transformedSum = Seq(
            Sum, Underscore, Grp(place, InMacro, Sp, places), Sp,
            Open, local, Plus, shift, Close);

        return Disp(new Formula.Aligned([
            Seq(
                places, Colon, Eq, placeSum, Comma, Sp,
                F.Id("AdelicPlace"), Open, finitePlaces, Comma, Sp,
                infinitePlaces, Close, Eq, places),
            Seq(
                ledger, Colon, Sp,
                Call("AdelicLocalLedger", finitePlaces, infinitePlaces), Comma, Sp,
                Call("Summable", Call("localContribution", ledger))),
            Seq(
                gauge, Colon, Sp,
                Call("ZeroSumGauge", finitePlaces, infinitePlaces), Comma, Sp,
                Call("HasSum", Call("shift", gauge), D(0))),
            Seq(
                completion, Open, ledger, Close, Colon, Eq, originalSum),
            Seq(
                Forall, Sp, finitePlaces, Comma, Sp, infinitePlaces, Colon, Sp,
                F.Id("Type"), Comma, Sp, Forall, Sp, ledger, Comma, Sp, gauge, Comma, Sp,
                completion, Open, Call("gaugeTransform", ledger, gauge), Close,
                Eq, transformedSum, Eq, originalSum, Eq,
                completion, Open, ledger, Close, Dot),
        ]));
    }
}
