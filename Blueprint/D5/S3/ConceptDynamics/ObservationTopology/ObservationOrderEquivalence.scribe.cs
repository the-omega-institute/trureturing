using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class ObservationOrderEquivalenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ObservationTopology/ObservationOrderEquivalence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorization equals partition-open inclusion; defects are antitone.",
        H("Observation Order Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinement-is-partition-open-inclusion"),
                DeclarationHandle.Create(
                    Prefix + "refines_iff_partition_open_inclusion"),
                H("Readout refinement is exactly partition-open inclusion"),
                StatementSource.FromAuthor(RefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A factorization of the coarse readout through the fine readout "
                            + "pulls every coarse observation-open set into the fine "
                            + "partition topology.")),
                    Paragraph(Text(
                        "On an inhabited source, the reverse open-set inclusion recovers "
                            + "fiber constancy of the coarse readout along fine fibers and "
                            + "hence a refinement factor.")),
                    Paragraph(Text(
                        "The equivalence is conditional on the displayed Nonempty source "
                            + "instance; no converse is asserted for an empty source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-defects-are-antitone-under-refinement"),
                DeclarationHandle.Create(
                    Prefix + "defectRelation_antitone_of_refines"),
                H("Target defects are antitone under readout refinement"),
                StatementSource.FromAuthor(AntitoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the coarse readout factor through the fine readout. Equality "
                            + "of fine observations then implies equality of coarse "
                            + "observations.")),
                    Paragraph(Text(
                        "A pair that is still indistinguishable to the fine readout while "
                            + "being distinguished by the target is therefore also a defect "
                            + "of the coarse readout.")),
                    Paragraph(Text(
                        "The conclusion is the displayed one-way subset inclusion; equality "
                            + "of defect relations is not claimed."))),
                DescribeRole.Theorem))));

    private static Formula RefinementFormula()
    {
        Formula state = F.Id("X");
        Formula coarseOutput = F.Id("Coarse");
        Formula fineOutput = F.Id("Fine");
        Formula coarse = F.Id("coarse");
        Formula fine = F.Id("fine");
        Formula instance = Seq(
            OpenBracket, Call("Nonempty", state), CloseBracket);
        Formula conclusion = Seq(
            Call("Refines", coarse, fine), Sp, Iff, Sp,
            Call(
                "ObservationOpenInclusion",
                Call("partitionTopology", coarse),
                Call("partitionTopology", fine)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, coarse, Colon, Sp, Call("Concept", state, coarseOutput),
            Comma, Sp,
            fine, Colon, Sp, Call("Concept", state, fineOutput), Comma,
            RowBreak, Grp(),
            Open, instance, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula AntitoneFormula()
    {
        Formula state = F.Id("X");
        Formula coarseOutput = F.Id("Coarse");
        Formula fineOutput = F.Id("Fine");
        Formula targetOutput = F.Id("Target");
        Formula coarse = F.Id("coarse");
        Formula fine = F.Id("fine");
        Formula target = F.Id("target");
        Formula refinement = F.Id("refinement");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, coarse, Colon, Sp, Call("Concept", state, coarseOutput),
            Comma, Sp,
            fine, Colon, Sp, Call("Concept", state, fineOutput), Comma,
            RowBreak, Grp(),
            target, Colon, Sp, Call("Concept", state, targetOutput), Comma, Sp,
            refinement, Colon, Sp, Call("Refines", coarse, fine), Comma,
            RowBreak, Grp(),
            Call("defectRelation", fine, target), Sp, Subseteq, Sp,
            Call("defectRelation", coarse, target), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
