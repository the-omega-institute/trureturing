using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity;

internal sealed class SubfamilyReadoutRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every dependent subfamily readout factors through the complete family readout.",
        H("Subfamily Readout Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-family-refines-every-subfamily-readout"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/"
                        + "SubfamilyReadoutRefinement."
                        + "subfamily_readout_refined_by_full_family"),
                H("The complete family refines every subfamily readout"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a dependent family of readouts on X and let J be any subset "
                            + "of its index type. The selected observation is the imported "
                            + "jointReadout instantiated on the subtype J.")),
                    Paragraph(Text(
                        "A complete output tuple restricts to J by discarding all coordinates "
                            + "outside the subfamily. This coordinate restriction factors the "
                            + "subfamily readout through the complete readout.")),
                    Paragraph(Text(
                        "Here Refines takes the coarser readout first and the finer readout "
                            + "second. Thus the theorem states Refines of the J-readout by the "
                            + "full-family readout, including empty and infinite families."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula valueFamily = F.Id("V");
        Formula readouts = F.Id("q");
        Formula subfamily = F.Id("J");
        Formula index = F.Id("i");
        Formula type = TypeUniverse();
        Formula readoutType = Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Arrow(stateType, Call("V", index)));
        Formula selectedReadout =
            Call("jointReadout", Call("restrict", readouts, subfamily));
        Formula completeReadout = Call("jointReadout", readouts);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Colon, Sp,
                type, Comma),
            Seq(
                valueFamily, Colon, Sp, Arrow(indexType, type), Comma, Sp,
                readouts, Colon, Sp, readoutType, Comma),
            Seq(
                subfamily, Sp, Subseteq, Sp, indexType, Comma, Sp,
                Call("Refines", selectedReadout, completeReadout), Dot),
        ]));
    }
}
