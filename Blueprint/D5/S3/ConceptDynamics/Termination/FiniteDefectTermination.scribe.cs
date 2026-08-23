using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Termination;

internal sealed class FiniteDefectTerminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict defect removal on a finite carrier stops within the initial defect count.",
        H("Finite Defect Termination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-defect-repairs-terminate"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Termination/FiniteDefectTermination."
                        + "finite_defect_repairs_terminate"),
                H("Finite strict defect repair terminates"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("W"), Colon, Sp, Operatorname,
                    Grp(F.Id("Type")), Comma, Sp,
                    F.Id("defects"), Colon, Sp, F.Id("Nat"), Sp, To, Sp,
                    Operatorname, Grp(F.Id("Set")), Open, F.Id("W"), Close,
                    Comma, RowBreak, Grp(),
                    Open,
                    Operatorname, Grp(F.Id("Finite")), Open, F.Id("W"), Close,
                    Sp, Land, RowBreak, Grp(),
                    Open,
                    Forall, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
                    Operatorname, Grp(F.Id("defects")), Open, F.Id("n"), Close,
                    Sp, Neq, Sp, Emptyset, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("defects")), Open,
                    F.Id("n"), Sp, Plus, Sp, D(1), Close,
                    Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("defects")), Open, F.Id("n"), Close,
                    Close, Sp, Land, RowBreak, Grp(),
                    Open,
                    Forall, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
                    Operatorname, Grp(F.Id("defects")), Open,
                    F.Id("n"), Sp, Plus, Sp, D(1), Close,
                    Sp, Subseteq, Sp,
                    Operatorname, Grp(F.Id("defects")), Open, F.Id("n"), Close,
                    Close,
                    Close, Sp, Rightarrow, RowBreak, Grp(),
                    Exists, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
                    F.Id("n"), Sp, Leq, Sp,
                    Operatorname, Grp(F.Id("ncard")), Open,
                    Operatorname, Grp(F.Id("defects")), Open, D(0), Close,
                    Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("defects")), Open, F.Id("n"), Close,
                    Sp, Eq, Sp, Emptyset, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The defect sequence is an independent source primitive on the finite "
                            + "carrier. Its initial set determines the public stopping bound.")),
                    Paragraph(Text(
                        "Strict change while defects remain and no-new-defects inclusion are "
                            + "separate public premises; together they give proper set descent.")),
                    Paragraph(Text(
                        "Strict inclusion lowers finite set cardinality at every nonterminal "
                            + "step. After at most the initial cardinality, zero cardinality "
                            + "forces the defect set to be empty."))),
                DescribeRole.Theorem))));
}
