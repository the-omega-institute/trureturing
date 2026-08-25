using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class OutcomeCorrectnessWithoutProcedureAuditDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Audits/OutcomeCorrectnessWithoutProcedureAudit."
            + "correct_outcome_can_lack_procedure_auditability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact target judgment can coexist with a procedure certificate that the audit log "
            + "cannot recover.",
        H("Outcome Correctness Without Procedure Auditability"),
        Blocks(Describe.Lean(
            DescribeId.Create("correct-outcome-can-lack-procedure-auditability"),
            DeclarationHandle.Create(Declaration),
            H("A correct outcome need not be procedurally auditable"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary Boolean target, the exhibited judgment returns that target "
                        + "exactly. Thus factual correctness is held fixed rather than inferred "
                        + "from the procedure channels.")),
                Paragraph(Text(
                    "The authorization channel distinguishes the two Boolean cases, while rules, "
                        + "hearing, provenance, and the audit log are constant. The canonical "
                        + "nested concept join therefore distinguishes cases that the log merges, "
                        + "so its procedure certificate cannot factor through the log.")),
                Paragraph(Text(
                    "The public statement exposes the four source channels, their canonical join, "
                        + "the judgment-target equality, and the failed refinement directly."))),
            DescribeRole.Theorem))));

    private static Formula Concept(Formula state, Formula value) =>
        Call("Concept", state, value);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula target = F.Id("T");
        Formula rules = F.Id("R");
        Formula authorization = F.Id("A");
        Formula hearing = F.Id("H");
        Formula provenance = F.Id("P");
        Formula judgment = F.Id("J");
        Formula log = F.Id("L");
        Formula booleanReadout = Concept(boolean, boolean);
        Formula unitReadout = Concept(boolean, unit);
        Formula procedureCertificate =
            Join(Join(Join(rules, authorization), hearing), provenance);
        Formula clauses = And(
            Seq(judgment, Sp, Eq, Sp, target),
            new Formula.Not(Call("Refines", procedureCertificate, log)));
        Formula countermodel = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(FormulaIdentifier.Create("R"), unitReadout),
                new(FormulaIdentifier.Create("A"), booleanReadout),
                new(FormulaIdentifier.Create("H"), unitReadout),
                new(FormulaIdentifier.Create("P"), unitReadout),
                new(FormulaIdentifier.Create("J"), booleanReadout),
                new(FormulaIdentifier.Create("L"), unitReadout),
            ],
            clauses);

        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("T"),
            booleanReadout,
            countermodel));
    }
}
