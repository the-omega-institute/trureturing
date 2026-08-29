using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TargetRisk;

internal sealed class LocalGlobalResidualExpressibilityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/TargetRisk/LocalGlobalResidualExpressibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The local-global target residual is empty exactly for expressible targets.",
        H("Local-Global Residual and Target Expressibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-global-target-residual"),
                DeclarationHandle.Create(DeclarationPrefix + "localGlobalResidual"),
                H("The residual collects locally merged but target-separated pairs"),
                StatementSource.FromAuthor(ResidualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The local-global residual of a target against a family of local "
                        + "readouts is the set of state pairs that every local readout "
                        + "merges while the target separates them. It reuses the canonical "
                        + "defect relation rather than introducing a second definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("residual-empty-iff-target-expressible"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "local_global_residual_empty_iff_expressible"),
                H("Emptiness of the residual characterises expressibility"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The residual is empty precisely when the target refines the "
                        + "effective joint readout, that is, when the target is expressible "
                        + "from the local observations alone.")),
                    Paragraph(Text(
                        "The proof applies the complete-observation expressibility "
                        + "equivalence already available in the repository instead of "
                        + "reproving it."))),
                DescribeRole.Theorem))));

    private static Formula Residual(Formula target, Formula family) =>
        new Formula.Apply(F.Id("LGRes"), [target, family]);

    private static Formula ResidualFormula()
    {
        Formula target = F.Id("T");
        Formula family = F.Id("q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula index = F.Id("i");
        Formula merged = Seq(
            Forall, Sp, index, Comma, Sp,
            new Formula.Relation(
                new Formula.Apply(new Formula.Subscript(family, index), [left]),
                FormulaRelationOperator.Equal,
                new Formula.Apply(new Formula.Subscript(family, index), [right])));
        Formula separated = new Formula.Relation(
            new Formula.Apply(target, [left]),
            FormulaRelationOperator.NotEqual,
            new Formula.Apply(target, [right]));
        return Disp(new Formula.Relation(
            Residual(target, family),
            FormulaRelationOperator.Equal,
            Seq(
                Open, left, Comma, Sp, right, Close, Sp,
                new Formula.Logic(merged, FormulaLogicOperator.And, separated))));
    }

    private static Formula CriterionFormula()
    {
        Formula target = F.Id("T");
        Formula family = F.Id("q");
        Formula empty = new Formula.Relation(
            Residual(target, family),
            FormulaRelationOperator.Equal,
            Emptyset);
        Formula expressible = new Formula.Apply(
            F.Id("Refines"),
            [target, new Formula.Apply(F.Id("effectiveReadout"), [family])]);
        return Disp(new Formula.Logic(
            empty, FormulaLogicOperator.Iff, expressible));
    }
}
