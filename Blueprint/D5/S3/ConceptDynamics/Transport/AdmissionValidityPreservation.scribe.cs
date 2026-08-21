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

    private static Formula Admission(Formula carrier, Formula state) =>
        Apply(Seq(Operatorname, Grp(F.Id("Adm")), Underscore, Grp(carrier)), state);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula transport = F.Id("h");
        Formula predicate = F.Id("P");
        Formula mappedX = Apply(transport, x);
        Formula pullback = Seq(Open, predicate, Sp, Circ, Sp, transport, Close);

        return Disp(Seq(
            Open, Forall, Sp, y, Comma, Sp,
            Admission(target, y), Sp, Rightarrow, Sp, Apply(predicate, y), Close,
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp,
            Admission(source, x), Sp, Rightarrow, Sp,
            Admission(target, mappedX), Close,
            RowBreak, Grp(),
            Rightarrow, Sp, Forall, Sp, x, Comma, Sp,
            Admission(source, x), Sp, Rightarrow, Sp, Apply(pullback, x), Dot));
    }
}
