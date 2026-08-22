using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class MultiTargetMinimalSufficiencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dependent joint target is the coarsest concept sufficient for every target.",
        H("Minimal Sufficiency for Multiple Targets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("multi-target-minimal-sufficiency"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency."
                        + "multi_target_minimal_sufficiency"),
                H("The joint target is minimally sufficient"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a dependent family of targets, the canonical joint target sends "
                            + "each state to the function listing every target value at that state.")),
                    Paragraph(Text(
                        "A readout factors every component target exactly when the joint target "
                            + "factors through it. Evaluation at an index gives each component "
                            + "projection from the joint target.")),
                    Paragraph(Text(
                        "For any simultaneously sufficient candidate, choosing its component "
                            + "factor maps and assembling them pointwise gives a joint readout "
                            + "factorization. This is the stated coarsest-property."))),
                DescribeRole.Theorem))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula MinimalityFormula()
    {
        Formula x = F.Id("X");
        Formula index = F.Id("I");
        Formula targetType = Subscript(F.Id("Y"), F.Id("i"));
        Formula targetFamily = F.Id("Y");
        Formula targets = F.Id("T");
        Formula readout = F.Id("C");
        Formula readoutType = Subscript(F.Id("B"), F.Id("C"));
        Formula candidate = Subscript(F.Id("q"), F.Id("D"));
        Formula candidateType = F.Id("D");
        Formula joint = Call("jointTarget", targets);
        Formula component = Apply(targets, F.Id("i"));
        Formula allThroughReadout = Seq(
            Forall, Sp, F.Id("i"), InMacro, Sp, index, Comma, Sp,
            Refines(component, readout));
        Formula allThroughJoint = Seq(
            Forall, Sp, F.Id("i"), InMacro, Sp, index, Comma, Sp,
            Refines(component, joint));
        Formula allThroughCandidate = Seq(
            Forall, Sp, F.Id("i"), InMacro, Sp, index, Comma, Sp,
            Refines(component, candidate));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, x, Comma, Sp, index, Comma, Sp, readoutType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            targetFamily, Colon, Sp, index, Sp, To, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            targets, Colon, Sp, Forall, Sp, F.Id("i"), InMacro, Sp, index,
            Comma, Sp, x, Sp, To, Sp, targetType, Comma, RowBreak, Grp(),
            readout, Colon, Sp, x, Sp, To, Sp, readoutType, Comma, RowBreak, Grp(),
            Open, Open, allThroughReadout, Close, Sp, Iff, Sp,
            Refines(joint, readout), Close, Sp, Land, RowBreak, Grp(),
            Open, allThroughJoint, Close, Sp, Land, RowBreak, Grp(),
            Forall, Sp, candidateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            candidate, Colon, Sp, x, Sp, To, Sp, candidateType, Comma, Sp,
            Open, allThroughCandidate, Close, Sp, Rightarrow, Sp,
            Refines(joint, candidate), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Subscript(Formula value, Formula subscript) =>
        Seq(value, Underscore, Grp(subscript));
}
