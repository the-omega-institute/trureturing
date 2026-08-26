using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class LocalGlobalResidualCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/LocalGlobalResidualCriterion."
            + "local_global_residual_empty_iff_joint_injective";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dependent residual of distinct states invisible to every local readout is empty "
            + "exactly when the joint readout is injective.",
        H("Local-Global Residual Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("local-global-residual-empty-iff-joint-injective"),
            DeclarationHandle.Create(Declaration),
            H("Residual emptiness is joint injectivity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an indexed dependent family q_i : X -> V_i, the residual is the "
                        + "dependent type of pairs of distinct states whose readings agree at "
                        + "every index.")),
                Paragraph(Text(
                    "Emptiness of this residual says that coordinatewise equality separates "
                        + "states. The canonical jointReadout packages exactly those coordinate "
                        + "values, so the frozen joint-faithfulness criterion identifies this "
                        + "separation property with injectivity."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula output = F.Id("V");
        Formula readout = F.Id("q");
        Formula index = F.Id("i");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula Pair(Formula x, Formula y) =>
            Seq(Open, x, Comma, Sp, y, Close);
        Formula Read(Formula i, Formula x) => Call("q", i, x);
        Formula residual = Seq(
            OpenBrace, Pair(left, right), Colon, Sp,
            stateType, Sp, Times, Sp, stateType, Sp, Mid, Sp,
            left, Sp, Neq, Sp, right, Sp, Land, Sp,
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Equal(Read(index, left), Read(index, right)), CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Colon, Sp, type, Comma, Sp,
                output, Colon, Sp, indexType, Sp, To, Sp, type, Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
                stateType, Sp, To, Sp, Call("V", index), Comma),
            Seq(
                Call("IsEmpty", residual), Sp, Iff, Sp,
                Call("Injective", Call("jointReadout", readout)), Dot),
        ]));
    }
}
