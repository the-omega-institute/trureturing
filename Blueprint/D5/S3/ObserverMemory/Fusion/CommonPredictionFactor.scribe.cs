using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class CommonPredictionFactorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dynamics-stable common prediction quotient has a unique surjective factor.",
        H("Common Prediction Factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-prediction-factor-has-the-universal-property"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Fusion/CommonPredictionFactor."
                        + "common_prediction_factor_universal_property"),
                H("The common prediction factor has the universal property"),
                StatementSource.FromAuthor(UniversalPropertyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let u update source states, and let q1 and q2 be readouts. Each "
                            + "readout determines the canonical complete-itinerary kernel. "
                            + "Their common relation is constructed as the least equivalence "
                            + "relation containing both kernels and preserved by u.")),
                    Paragraph(Text(
                        "Suppose a surjection r onto W intertwines u with an update v on W. "
                            + "Also suppose r factors through each complete-itinerary quotient "
                            + "by maps a1 and a2. Then there is a unique surjective map h from "
                            + "the common quotient to W, and h factors the canonical projection.")),
                    Paragraph(Text(
                        "The two given factorizations put both itinerary kernels inside the "
                            + "kernel of r, while the intertwining equation makes that kernel "
                            + "stable under u. The infimum construction therefore lies inside "
                            + "the kernel of r. Pinned Mathlib quotient lift, surjectivity, and "
                            + "uniqueness results then supply the asserted map directly."))),
                DescribeRole.Theorem))));

    private static Formula QuotientOf(Formula relation) =>
        Seq(Operatorname, Grp(F.Id("Quotient")), Open, relation, Close);

    private static Formula Projection(Formula readout) =>
        Seq(Pi, Underscore, Grp(readout));

    private static Formula UniversalPropertyFormula()
    {
        Formula stateType = F.Id("Y");
        Formula firstOutput = Seq(F.Id("O"), Underscore, Grp(D(1)));
        Formula secondOutput = Seq(F.Id("O"), Underscore, Grp(D(2)));
        Formula factorType = F.Id("W");
        Formula update = F.Id("u");
        Formula factorUpdate = F.Id("v");
        Formula firstReadout = Seq(F.Id("q"), Underscore, Grp(D(1)));
        Formula secondReadout = Seq(F.Id("q"), Underscore, Grp(D(2)));
        Formula factor = F.Id("r");
        Formula fromFirst = Seq(F.Id("a"), Underscore, Grp(D(1)));
        Formula fromSecond = Seq(F.Id("a"), Underscore, Grp(D(2)));
        Formula firstRelation = Call("KerTr", update, firstReadout);
        Formula secondRelation = Call("KerTr", update, secondReadout);
        Formula commonRelation = Call("StableJoin", update, firstRelation, secondRelation);
        Formula commonProjection = Seq(Pi, Underscore, Grp(F.Id("common")));
        Formula descend = F.Id("h");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, firstOutput, Comma, Sp,
            secondOutput, Comma, Sp, factorType, Comma, RowBreak,
            update, Colon, Sp, stateType, Sp, To, Sp, stateType, Comma, Sp,
            factorUpdate, Colon, Sp, factorType, Sp, To, Sp, factorType, Comma, RowBreak,
            firstReadout, Colon, Sp, stateType, Sp, To, Sp, firstOutput, Comma, Sp,
            secondReadout, Colon, Sp, stateType, Sp, To, Sp, secondOutput, Comma, RowBreak,
            factor, Colon, Sp, stateType, Sp, To, Sp, factorType, Comma, Sp,
            Call("Surjective", factor), Comma, RowBreak,
            factor, Sp, Circ, Sp, update, Sp, Eq, Sp,
            factorUpdate, Sp, Circ, Sp, factor, Comma, RowBreak,
            fromFirst, Colon, Sp, QuotientOf(firstRelation), Sp, To, Sp, factorType,
            Comma, Sp, fromSecond, Colon, Sp, QuotientOf(secondRelation), Sp, To, Sp,
            factorType, Comma, RowBreak,
            factor, Sp, Eq, Sp, fromFirst, Sp, Circ, Sp,
            Projection(firstReadout), Comma, Sp,
            factor, Sp, Eq, Sp, fromSecond, Sp, Circ, Sp,
            Projection(secondReadout), Sp, Rightarrow, RowBreak,
            Exists, Bang, Sp, descend, Colon, Sp, QuotientOf(commonRelation), Sp,
            To, Sp, factorType, Comma, Sp, Call("Surjective", descend), Sp, Land,
            RowBreak, factor, Sp, Eq, Sp, descend, Sp, Circ, Sp,
            commonProjection, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
