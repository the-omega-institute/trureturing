using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Closure;

internal sealed class SourceClosureLawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closure operator is extensive and monotone on source sets.",
        H("Source Closure Laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-closure-extensive-and-monotone"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Closure/SourceClosureLaws."
                    + "source_closure_extensive_and_monotone"),
            H("Closure is extensive and monotone"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The closure object is the canonical Mathlib ClosureOperator on the "
                        + "source set carrier; no target-defined closure is introduced.")),
                Paragraph(Text(
                    "Its first public clause contains every source set in its closure, and "
                        + "its second clause transports every inclusion S subset T to closure "
                        + "S subset closure T.")),
                Paragraph(Text(
                    "The proof directly applies ClosureOperator.le_closure and monotone. "
                        + "The pinned repository search found no stronger packaged theorem."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula SetOf(Formula element) =>
        Apply("Set", element);

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("Carrier");
        Formula closure = F.Id("cl");
        Formula source = F.Id("S");
        Formula target = F.Id("T");
        Formula setCarrier = SetOf(carrier);
        Formula closureType = Apply("ClosureOperator", setCarrier);
        Formula closureSource = Apply("cl", source);
        Formula closureTarget = Apply("cl", target);
        Formula inclusion = new Formula.Relation(
            source, FormulaRelationOperator.SubsetOf, closureSource);
        Formula monotone = new Formula.Logic(
            new Formula.Relation(source, FormulaRelationOperator.SubsetOf, target),
            FormulaLogicOperator.Implies,
            new Formula.Relation(closureSource, FormulaRelationOperator.SubsetOf, closureTarget));

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            closure, Colon, Sp, closureType, Comma, Sp,
            source, Comma, Sp, target, Colon, Sp, setCarrier, Comma, RowBreak, Grp(),
            inclusion, Sp, Land, Sp, Open, monotone, Close, Dot));
    }
}
