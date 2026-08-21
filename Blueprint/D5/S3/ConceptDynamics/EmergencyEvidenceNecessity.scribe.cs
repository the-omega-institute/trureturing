using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class EmergencyEvidenceNecessityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evidence collisions force an authorization error and block necessity recovery.",
        H("Emergency Evidence Necessity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("emergency-evidence-necessity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/EmergencyEvidenceNecessity.emergency_evidence_necessity"),
                H("Evidence-only authorization must err on a collision"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public hypotheses expose the evidence interface and Boolean "
                            + "necessity target, together with an equal-evidence, unequal-necessity "
                            + "pair.")),
                    Paragraph(Text(
                        "For every Boolean rule on evidence, the theorem explicitly exhibits an "
                            + "unnecessary authorization or a necessary rejection. The same collision "
                            + "also prevents any recovery map from factoring necessity through evidence.")),
                    Paragraph(Text(
                        "The nonfactorization conjunct directly applies the repository's "
                            + "`informed_disclosure_defect` theorem."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Formula()
    {
        Formula state = F.Id("X");
        Formula evidenceType = Subscript(F.Id("B"), F.Id("E"));
        Formula evidence = F.Id("E");
        Formula necessity = F.Id("N");
        Formula authorize = F.Id("A");
        Formula recover = F.Id("R");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula same = Seq(Apply(evidence, x), Sp, Eq, Sp, Apply(evidence, y));
        Formula different = Seq(Apply(necessity, x), Sp, Neq, Sp, Apply(necessity, y));
        Formula unnecessary = Seq(Open, Exists, Sp, z, Comma, Sp,
            Apply(necessity, z), Sp, Eq, Sp, F.Id("false"), Sp, Land, Sp,
            Apply(authorize, Apply(evidence, z)), Sp, Eq, Sp, F.Id("true"), Close);
        Formula rejected = Seq(Open, Exists, Sp, z, Comma, Sp,
            Apply(necessity, z), Sp, Eq, Sp, F.Id("true"), Sp, Land, Sp,
            Apply(authorize, Apply(evidence, z)), Sp, Eq, Sp, F.Id("false"), Close);
        Formula errors = Seq(
            Open, Forall, Sp, authorize, Colon, Sp, Arrow(evidenceType, F.Id("Bool")), Comma, Sp,
            unnecessary, Sp, Lor, Sp, rejected, Close);
        Formula noRecovery = Seq(Neg, Open, Exists, Sp, recover, Colon, Sp,
            Arrow(evidenceType, F.Id("Bool")), Comma, Sp,
            necessity, Sp, Eq, Sp,
            Compose(recover, evidence), Close);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, evidenceType, Comma, Esc,
            evidence, Colon, Sp, Arrow(state, evidenceType), Comma, Sp,
            necessity, Colon, Sp, Arrow(state, F.Id("Bool")), Comma, Sp,
            Forall, Sp, x, Comma, Sp, y, Comma, Esc,
            Open, same, Sp, Land, Sp, different, Close, Sp, Rightarrow, Sp,
            Open, errors, Sp, Land, Sp, noRecovery, Close, Dot));
    }

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
