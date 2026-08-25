using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class IncompleteTestCoverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Passing a strict partial coverage cannot establish an empty defect set.",
        H("Incomplete Test Coverage"),
        Blocks(Describe.Lean(
            DescribeId.Create("passed-partial-tests-leave-a-possible-defect"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Audits/IncompleteTestCoverage."
                    + "passed_partial_tests_leave_a_possible_defect"),
            H("Partial tests leave a possible defect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The covered set and the full defect set are independent source "
                        + "predicates; strict inclusion records that the test family does "
                        + "not cover every possible defect.")),
                Paragraph(Text(
                    "The all-tests-pass premise says every covered candidate is excluded. "
                        + "The public conclusion exposes both that the covered candidates are "
                        + "empty after passing and that an uncovered defect remains.")),
                Paragraph(Text(
                    "The proof applies the pinned Set.ssubset_iff_exists and set-extensionality "
                        + "lemmas directly. No completeness certificate is assumed or hidden."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula TheoremFormula()
    {
        Formula candidateType = F.Id("Candidate");
        Formula covered = F.Id("covered");
        Formula defects = F.Id("defects");
        Formula candidate = F.Id("d");
        Formula setType = Apply("Set", candidateType);
        Formula strict = Apply("ssubset", covered, defects);
        Formula passingClean = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            candidateType,
            new Formula.Logic(
                Member(candidate, covered), FormulaLogicOperator.Implies,
                Seq(Neg, Sp, Member(candidate, defects))));
        Formula coveredEmpty = new Formula.Relation(
            covered, FormulaRelationOperator.Equal, Emptyset);
        Formula defectWitness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("d"),
            candidateType,
            Member(candidate, defects));

        return Disp(Seq(
            Forall, Sp, candidateType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            covered, Comma, Sp, defects, Colon, Sp, setType, Comma, RowBreak, Grp(),
            strict, Sp, Land, Sp, passingClean, Sp, Rightarrow, RowBreak, Grp(),
            coveredEmpty, Sp, Land, Sp, defectWitness, Dot));
    }
}
