using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class ProcedureDerivedCorrectOutcomeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Audits/ProcedureDerivedCorrectOutcome."
            + "procedure_derived_correct_outcome_can_lack_auditability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A judgment computed from a four-channel procedure certificate can match its target "
            + "even when the audit log cannot recover that certificate.",
        H("Procedure-Derived Correct Outcome"),
        Blocks(Describe.Lean(
            DescribeId.Create("procedure-derived-correct-outcome-can-lack-auditability"),
            DeclarationHandle.Create(Declaration),
            H("Correct output does not imply procedure auditability"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The rules, authorization, hearing, and provenance readouts form the "
                        + "canonical nested procedure certificate. The displayed judgment is "
                        + "the oracle composed with that certificate, so it is not an "
                        + "independent witness chosen equal to the target.")),
                Paragraph(Text(
                    "The construction uses an authorization readout that retains the Boolean "
                        + "case. It therefore supports exact target recovery while making the "
                        + "same certificate distinguish two cases merged by the constant log.")),
                Paragraph(Text(
                    "Thus the positive equality and the failed refinement are consequences of "
                        + "one shared procedure construction."))),
            DescribeRole.Theorem))));

    private static Formula Concept(Formula state, Formula value) =>
        Call("Concept", state, value);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Product(Formula first, Formula second) =>
        Seq(Open, first, Sp, Times, Sp, second, Close);

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
        Formula log = F.Id("L");
        Formula oracle = F.Id("oracle");
        Formula targetImage = Call("TargetImage", F.Id("identityBool"));
        Formula unitReadout = Concept(boolean, unit);
        Formula authorizationReadout = Concept(boolean, targetImage);
        Formula firstCertificateType = Product(unit, targetImage);
        Formula secondCertificateType = Product(firstCertificateType, unit);
        Formula procedureType = Product(secondCertificateType, unit);
        Formula procedureCertificate =
            Join(Join(Join(rules, authorization), hearing), provenance);
        Formula correctJudgment = Seq(
            oracle, Sp, Circ, Sp, procedureCertificate, Sp, Eq, Sp, target);
        Formula clauses = And(
            correctJudgment,
            new Formula.Not(Call("Refines", procedureCertificate, log)));
        Formula countermodel = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(FormulaIdentifier.Create("R"), unitReadout),
                new(FormulaIdentifier.Create("A"), authorizationReadout),
                new(FormulaIdentifier.Create("H"), unitReadout),
                new(FormulaIdentifier.Create("P"), unitReadout),
                new(FormulaIdentifier.Create("L"), unitReadout),
                new(FormulaIdentifier.Create("oracle"), Arrow(procedureType, boolean)),
            ],
            clauses);

        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("T"),
            Concept(boolean, boolean),
            countermodel));
    }
}
