using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class ProjectionCommutatorCrossBlockCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A canonical orthogonal projection commutes with an operator exactly when both directed cross blocks vanish.",
        H("Projection Commutator Cross-Block Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projection-commutator-cross-blocks"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/BlockStructure/ProjectionCommutatorCrossBlockCriterion."
                        + "projection_commutator_cross_blocks"),
                H("A projection commutator is controlled by its two cross blocks"),
                StatementSource.FromAuthor(CrossBlockCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be a subspace of a real or complex Hilbert carrier that admits "
                            + "its canonical orthogonal projection P, and set Q to one minus P. "
                            + "For every bounded linear operator T, the commutator of P and T is "
                            + "PTQ minus QTP.")),
                    Paragraph(Text(
                        "Multiplying a zero commutator by P and Q isolates PTQ; multiplying in "
                            + "the opposite order isolates the negative of QTP. Idempotence and "
                            + "orthogonality of the canonical projection make both diagonal "
                            + "terms disappear. Conversely, two zero cross blocks make their "
                            + "difference zero."))),
                DescribeRole.Theorem))));

    private static Formula Product(Formula left, Formula middle, Formula right) =>
        Multiply(Multiply(left, middle), right);

    private static Formula CrossBlockCriterionFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula visible = F.Id("V");
        Formula map = F.Id("T");
        Formula projection = Call("starProjection", visible);
        Formula complement = Subtract(D(1), projection);
        Formula commutator = Call("commutator", projection, map);
        Formula visibleResidual = Product(projection, map, complement);
        Formula residualVisible = Product(complement, map, projection);
        Formula identity = Equal(
            commutator,
            Subtract(visibleResidual, residualVisible));
        Formula vanishing = Seq(
            Equal(commutator, D(0)), Sp, Iff, Sp,
            Open, Equal(visibleResidual, D(0)), Sp, Land, Sp,
            Equal(residualVisible, D(0)), Close);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp,
            visible, Comma, Sp, map, Comma,
            RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", space), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, space), Sp, Land,
            RowBreak, Grp(),
            visible, Sp, InMacro, Sp, Call("Submodule", scalar, space), Sp,
            Land, Sp, Call("HasOrthogonalProjection", visible), Sp, Land, Sp,
            map, Sp, InMacro, Sp, Call("ContinuousLinearMap", scalar, space, space),
            Sp, Rightarrow,
            RowBreak, Grp(),
            Open, identity, Sp, Land, Sp, Open, vanishing, Close, Close, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
