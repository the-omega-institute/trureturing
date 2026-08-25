using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity;

internal sealed class SubfamilyInadequacyPersistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target inadequacy for a full readout family persists under every subfamily restriction.",
        H("Subfamily Inadequacy Persistence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-family-inadequacy-persists-to-every-subfamily"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/"
                        + "SubfamilyInadequacyPersistence."
                        + "full_family_inadequacy_persists_to_subfamilies"),
                H("No subfamily repairs full-family inadequacy"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a dependent family of readouts on X and let T be a target. "
                            + "The full observation is the imported jointReadout q; the "
                            + "observation associated with a subset J is the same jointReadout "
                            + "instantiated on the subtype J.")),
                    Paragraph(Text(
                        "Any decoder from the restricted readout also decodes from the full "
                            + "readout after restricting a full output tuple to coordinates in "
                            + "J. Therefore adequacy of one subfamily would imply adequacy of "
                            + "the full family, contradicting the premise.")),
                    Paragraph(Text(
                        "The quantifier ranges over every subset of the index type, so finite, "
                            + "countable, and full selections are all included without separate "
                            + "cardinality assumptions."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula targetType = F.Id("Y");
        Formula valueFamily = F.Id("V");
        Formula readouts = F.Id("q");
        Formula target = F.Id("T");
        Formula subfamily = F.Id("J");
        Formula index = F.Id("i");
        Formula type = TypeUniverse();
        Formula readoutType = Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Arrow(stateType, Call("V", index)));
        Formula fullAdequacy = Call(
            "TargetAdequate", Call("jointReadout", readouts), target);
        Formula restrictedAdequacy = Call(
            "TargetAdequate",
            Call("jointReadout", Call("restrict", readouts, subfamily)),
            target);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Comma, Sp,
                targetType, Colon, Sp, type, Comma),
            Seq(
                valueFamily, Colon, Sp, Arrow(indexType, type), Comma, Sp,
                readouts, Colon, Sp, readoutType, Comma),
            Seq(
                target, Colon, Sp, Arrow(stateType, targetType), Comma),
            Seq(
                Neg, Sp, Open, fullAdequacy, Close, Sp, Rightarrow, Sp,
                Forall, Sp, subfamily, Sp, Subseteq, Sp, indexType, Comma, Sp,
                Neg, Sp, Open, restrictedAdequacy, Close, Dot),
        ]));
    }
}
