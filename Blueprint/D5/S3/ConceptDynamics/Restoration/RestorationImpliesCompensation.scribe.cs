using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Restoration;

internal sealed class RestorationImpliesCompensationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity restoration preserves every value determined by identity.",
        H("Restoration Implies Compensation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("identity-restoration-implies-value-compensation"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Restoration/RestorationImpliesCompensation."
                        + "identity_restoration_implies_value_compensation"),
                H("Identity restoration implies value compensation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let I record identity, let V record value or function, let U be "
                            + "the harm process, and let R be the repair process.")),
                    Paragraph(Text(
                        "The refinement premise supplies a map from identity values to "
                            + "value values. Applying that map to the restored identity "
                            + "equality yields value compensation at every state."))),
                DescribeRole.Theorem))));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula identityCarrier = Subscript(F.Id("B"), F.Id("I"));
        Formula valueCarrier = Subscript(F.Id("B"), F.Id("V"));
        Formula identity = F.Id("I");
        Formula value = F.Id("V");
        Formula harm = F.Id("U");
        Formula repair = F.Id("R");
        Formula x = F.Id("x");
        Formula repaired = At(repair, At(harm, x));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula refines = Seq(
            Operatorname, Grp(F.Id("Refines")), Open, value, Comma, Sp, identity, Close);
        Formula identityRestored = Seq(
            Forall, Sp, x, Comma, Sp, At(identity, repaired), Sp, Eq, Sp, At(identity, x));
        Formula valueRestored = Seq(
            Forall, Sp, x, Comma, Sp, At(value, repaired), Sp, Eq, Sp, At(value, x));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            state, Comma, Sp, identityCarrier, Comma, Sp, valueCarrier,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            identity, Colon, Sp, state, Sp, To, Sp, identityCarrier, Comma, Sp,
            value, Colon, Sp, state, Sp, To, Sp, valueCarrier, Comma, RowBreak, Grp(),
            harm, Comma, Sp, repair, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            refines, Comma, RowBreak, Grp(),
            identityRestored, Comma, RowBreak, Grp(),
            Rightarrow, Sp, valueRestored, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
