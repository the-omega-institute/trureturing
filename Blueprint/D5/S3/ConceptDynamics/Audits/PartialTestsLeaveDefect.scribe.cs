using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class PartialTestsLeaveDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial tests can pass while a disjoint nonempty defect set remains.",
        H("Partial Tests Leave a Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("passing-partial-tests-can-leave-a-defect"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Audits/PartialTestsLeaveDefect."
                    + "passing_partial_tests_can_leave_a_defect"),
            H("Passing partial tests can leave a defect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The Boolean countermodel uses one covered set and one defect set "
                        + "throughout. Both are nonempty, they are disjoint, and every "
                        + "covered candidate is absent from the defect set.")),
                Paragraph(Text(
                    "Consequently the same construction witnesses both successful tests "
                        + "and a surviving defect; no completeness certificate is assumed.")),
                Paragraph(Text(
                    "Pinned Mathlib singleton and disjointness lemmas discharge the four "
                        + "public clauses directly. The Lean module introduces no definition."))),
            DescribeRole.Theorem))));

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula covered = F.Id("covered");
        Formula defects = F.Id("defects");
        Formula candidate = F.Id("candidate");
        Formula setType = Call("Set", boolean);
        Formula passing = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("candidate"),
            boolean,
            new Formula.Logic(
                Member(candidate, covered),
                FormulaLogicOperator.Implies,
                Seq(Neg, Sp, Member(candidate, defects))));

        return Disp(Seq(
            Exists, Sp, covered, Comma, Sp, defects, Colon, Sp, setType, Comma, RowBreak, Grp(),
            Call("Nonempty", covered), Sp, Land, Sp,
            Call("Nonempty", defects), Sp, Land, RowBreak, Grp(),
            Call("Disjoint", covered, defects), Sp, Land, Sp,
            passing, Dot));
    }
}
