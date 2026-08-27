using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class AdmissionValidityPreservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admission-preserving transport pulls target validity back to the source.",
        H("Validity Preservation by Admissible Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("validity-preserved-by-admission-map"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/AdmissionValidityPreservation."
                        + "validity_preserved_by_admission_map"),
                H("Validity is preserved by an admission map"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Validity in the target is the source's public quantifier: every target "
                            + "state satisfying the target admission predicate satisfies P.")),
                    Paragraph(Text(
                        "Admission preservation is the standard MapsTo condition on the source "
                            + "and target admission predicates. Both predicates and the transport "
                            + "map are independent inputs.")),
                    Paragraph(Text(
                        "For an admissible source state x, admission preservation supplies target "
                            + "admissibility of h(x), so target validity supplies P(h(x)), exactly "
                            + "the value of the pulled-back predicate at x."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula sourceAdmissible = F.Id("sourceAdmissible");
        Formula targetAdmissible = F.Id("targetAdmissible");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula transport = F.Id("h");
        Formula predicate = F.Id("P");
        Formula targetValid = F.Id("targetValid");
        Formula admissionPreserving = F.Id("admissionPreserving");
        Formula proposition = F.Id("Prop");
        Formula pullback = Seq(Open, predicate, Sp, Circ, Sp, transport, Close);
        Formula sourceSet = Seq(
            OpenBrace, x, Colon, Sp, source, Sp, Mid, Sp,
            Apply(sourceAdmissible, x), CloseBrace);
        Formula targetSet = Seq(
            OpenBrace, y, Colon, Sp, target, Sp, Mid, Sp,
            Apply(targetAdmissible, y), CloseBrace);
        Formula targetValidityLaw = Seq(
            Forall, Sp, y, Colon, Sp, target, Comma, Sp,
            Apply(targetAdmissible, y), Sp, Rightarrow, Sp, Apply(predicate, y));
        Formula admissionPreservingLaw = Call(
            "MapsTo", transport, sourceSet, targetSet);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, target, Colon, Sp, F.Id("Type"),
            Comma, RowBreak, Grp(),
            sourceAdmissible, Colon, Sp, Arrow(source, proposition), Comma, Sp,
            targetAdmissible, Colon, Sp, Arrow(target, proposition), Comma,
            RowBreak, Grp(),
            transport, Colon, Sp, Call("Concept", source, target), Comma, Sp,
            predicate, Colon, Sp, Arrow(target, proposition), Comma, RowBreak, Grp(),
            targetValid, Colon, Sp, Grp(targetValidityLaw), Comma, RowBreak, Grp(),
            admissionPreserving, Colon, Sp, admissionPreservingLaw, Comma,
            RowBreak, Grp(),
            Forall, Sp, x, Colon, Sp, source, Comma, Sp,
            Apply(sourceAdmissible, x), Sp, Rightarrow, Sp,
            Apply(pullback, x), Dot));
    }
}
