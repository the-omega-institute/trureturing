using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ZeroSumGaugeGlobalCompletionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero-sum redistribution preserves the global additive defect and the structural "
            + "completion signature K(C)/G.",
        H("Zero-Sum Gauge Invariance of the Structural Completion Signature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-sum-gauge-preserves-global-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion."
                        + "zero_sum_gauge_preserves_global_completion"),
                H("A zero-sum local gauge preserves the global defect and signature"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite and infinite place types are both nonempty, and their disjoint "
                            + "sum is the full place type. The defect codomain is any Hausdorff "
                            + "topological additive commutative group. An adelic local ledger is "
                            + "a summable family in that codomain, while ZeroSumGauge is the "
                            + "additive subgroup of summable shift families with total zero.")),
                    Paragraph(Text(
                        "The normalization set N is the full ledger space. GlobalCompletionPoint "
                            + "is the subtype K(C) of normalized ledgers whose globalAdditiveDefect "
                            + "vanishes. Zero-sum gauges act on K(C), and "
                            + "StructuralCompletionSignature is the orbit quotient K(C)/G.")),
                    Paragraph(Text(
                        "Summable.tsum_add proves that a gauge transform preserves "
                            + "globalAdditiveDefect, so it maps completion points to completion "
                            + "points. Quotient.sound then proves that every transformed completion "
                            + "point has the same structuralCompletionSignatureClass. These are the "
                            + "two conjuncts of the public theorem."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula finitePlaces = Seq(F.Id("V"), Underscore, Grp(F.Id("f")));
        Formula infinitePlaces = Seq(F.Id("V"), Underscore, Grp(Infty));
        Formula places = F.Id("V");
        Formula defectSpace = F.Id("D");
        Formula ledger = F.Id("L");
        Formula gauge = F.Id("b");
        Formula completionPoint = F.Id("k");
        Formula place = F.Id("v");
        Formula local = Seq(F.Id("L"), Underscore, Grp(place));
        Formula shift = Seq(F.Id("b"), Underscore, Grp(place));
        Formula globalDefect = Seq(Delta, Underscore, Grp(F.Id("glob")));
        Formula placeSum = Call("Sum", finitePlaces, infinitePlaces);
        Formula ledgerType = Call(
            "AdelicLocalLedger", finitePlaces, infinitePlaces, defectSpace);
        Formula gaugeGroup = Call(
            "ZeroSumGauge", finitePlaces, infinitePlaces, defectSpace);
        Formula normalization = Seq(F.Id("N"), Open, F.Id("C"), Close);
        Formula completionPoints = Seq(F.Id("K"), Open, F.Id("C"), Close);
        Formula gaugeAction = Seq(F.Id("G"), Open, F.Id("C"), Close);
        Formula signature = Seq(Sigma, Open, F.Id("C"), Close);
        Formula originalSum = Seq(
            Sum, Underscore, Grp(place, InMacro, Sp, places), Sp, local);
        Formula transformedSum = Seq(
            Sum, Underscore, Grp(place, InMacro, Sp, places), Sp,
            Open, local, Plus, shift, Close);
        Formula transformedLedger = Call("gaugeTransform", ledger, gauge);
        Formula transformedCompletionPoint =
            Call("gaugeTransformCompletionPoint", completionPoint, gauge);

        return Disp(new Formula.Aligned([
            Seq(
                finitePlaces, Comma, Sp, infinitePlaces, Colon, Sp, F.Id("Type"), Comma, Sp,
                Call("Nonempty", finitePlaces), Comma, Sp,
                Call("Nonempty", infinitePlaces)),
            Seq(
                defectSpace, Colon, Sp, F.Id("Type"), Comma, Sp,
                Call("AddCommGroup", defectSpace), Comma, Sp,
                Call("TopologicalSpace", defectSpace), Comma, Sp,
                Call("IsTopologicalAddGroup", defectSpace), Comma, Sp,
                Call("T2Space", defectSpace)),
            Seq(
                places, Colon, Eq, placeSum, Eq,
                Call("AdelicPlace", finitePlaces, infinitePlaces)),
            Seq(
                ledger, Colon, Sp, ledgerType, Comma, Sp,
                Call("Summable", Call("localContribution", ledger))),
            Seq(
                gauge, Colon, Sp, gaugeGroup, Comma, Sp,
                Call("HasSum", Call("shift", gauge), D(0))),
            Seq(
                globalDefect, Open, ledger, Close, Colon, Eq, originalSum),
            Seq(
                normalization, Eq, ledgerType),
            Seq(
                completionPoints, Eq, OpenBrace, ledger, InMacro, Sp, normalization, Mid,
                globalDefect, Open, ledger, Close, Eq, D(0), CloseBrace),
            Seq(
                gaugeAction, Eq, gaugeGroup, Comma, Sp,
                signature, Eq, completionPoints, Slash, gaugeAction),
            Seq(
                Forall, Sp, ledger, Comma, Sp, gauge, Comma, Sp,
                Open, globalDefect, Open, transformedLedger, Close,
                Eq, transformedSum, Eq, originalSum, Eq,
                globalDefect, Open, ledger, Close, Close, Sp, Land, RowBreak, Grp(),
                Open, Forall, Sp, completionPoint, Colon, Sp, completionPoints, Comma, Sp,
                Call("structuralCompletionSignatureClass", transformedCompletionPoint),
                Eq, Call("structuralCompletionSignatureClass", completionPoint), Close, Dot),
        ]));
    }
}
