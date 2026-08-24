using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class IndexedTargetDefectMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula targetType = F.Id("T");
        Formula observation = F.Id("q");
        Formula target = F.Id("t");
        Formula smaller = F.Id("J");
        Formula larger = F.Id("K");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula outputFamily = Seq(index, Sp, To, Sp, type);
        Formula observationFamily = Seq(
            Forall, Sp, F.Id("i"), Colon, Sp, index, Comma, Sp,
            state, Sp, To, Sp, Apply(output, F.Id("i")));
        Formula coarseReadout = Call("jointReadout", observation, smaller);
        Formula fineReadout = Call("jointReadout", observation, larger);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, index, Comma, Sp, state, Comma, Sp, targetType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            output, Colon, Sp, outputFamily, Comma, Sp,
            observation, Colon, Sp, observationFamily, Comma, RowBreak, Grp(),
            target, Colon, Sp, state, Sp, To, Sp, targetType,
            Comma, RowBreak, Grp(),
            smaller, Comma, Sp, larger, Colon, Sp, Call("Finset", index),
            Comma, Sp, smaller, Sp, Subseteq, Sp, larger, Sp, Rightarrow,
            RowBreak, Grp(),
            Call("defectRelation", fineReadout, target), Sp, Subseteq, Sp,
            Call("defectRelation", coarseReadout, target), Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Enlarging an indexed readout budget shrinks its target-defect relation.",
            H("Indexed Target-Defect Monotonicity"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("larger-observation-budget-shrinks-target-defect"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/RefinementFactorization/"
                            + "IndexedTargetDefectMonotonicity."
                            + "larger_observation_budget_shrinks_target_defect"),
                    H("Larger observation budgets shrink target defects"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "A single indexed observation family q constructs both public joint "
                                + "readouts by restricting q to J and K. The target-defect relation "
                                + "is the target-risk family's canonical predicate: equal readout "
                                + "coordinates together with unequal target values.")),
                        Paragraph(Text(
                            "When J is contained in K, the existing indexed-readout theorem sends "
                                + "equality of the K-readouts to equality of the J-readouts. The "
                                + "target inequality is unchanged, yielding the displayed reverse "
                                + "inclusion of defect relations.")),
                        Paragraph(Text(
                            "No sibling copy of the indexed readout, refinement relation, or defect "
                                + "predicate is introduced."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
