using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class HilbertResolutionHierarchyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform Hilbert resolution controls state-family and member-target residuals, while "
            + "proper projection stages obstruct uniform resolution.",
        H("Hilbert Resolution Hierarchy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-family-and-target-resolution-hierarchy"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Completion/HilbertResolutionHierarchy."
                        + "hilbert_resolution_hierarchy"),
                H("Uniform resolution implies family and target resolution"),
                StatementSource.FromAuthor(HierarchyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary orthogonally complemented Hilbert subspaces V(n), the "
                            + "residual is the canonical orthogonal complement V(n)-perp. The "
                            + "family residual is the extended nonnegative supremum of its "
                            + "projection norms, so empty and unbounded families remain defined.")),
                    Paragraph(Text(
                        "Operator-norm convergence to the identity forces the visible stage to "
                            + "be the whole space eventually, since every proper stage remains "
                            + "exactly one unit away. The family residual is then eventually zero.")),
                    Paragraph(Text(
                        "A member target is bounded by the same family's supremum. Finally, the "
                            + "frozen uniform-completion obstruction supplies both the norm-one "
                            + "identity and nonconvergence when every stage is proper."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Stage(Formula stages, Formula index) => Apply(stages, index);

    private static Formula Perpendicular(Formula space) => Seq(space, Caret, Grp(Perp));

    private static Formula Projection(Formula space, Formula vector) =>
        Apply(Call("P", space), vector);

    private static Formula ResidualNorm(
        Formula stages,
        Formula index,
        Formula vector) =>
        new Formula.Norm(Projection(Perpendicular(Stage(stages, index)), vector));

    private static Formula FamilyResidual(
        Formula stages,
        Formula index,
        Formula family,
        Formula member) =>
        Seq(
            Operatorname, Grp(F.Id("sup")), Underscore,
            Grp(member, InMacro, Sp, family), Sp,
            ResidualNorm(stages, index, member));

    private static Formula UniformNorm(Formula stages, Formula index) =>
        new Formula.Norm(Seq(
            F.Id("I"), Sp, Minus, Sp, Call("P", Stage(stages, index))));

    private static Formula LimitZero(Formula index, Formula expression) =>
        Seq(Call("lim", index, Infty, expression), Sp, Eq, Sp, D(0));

    private static Formula HierarchyFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula stages = F.Id("V");
        Formula family = F.Id("T");
        Formula target = F.Id("x");
        Formula member = F.Id("y");
        Formula index = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula submodule = Call("Submodule", scalar, space);
        Formula uniform = LimitZero(index, UniformNorm(stages, index));
        Formula familyResolution = LimitZero(
            index, FamilyResidual(stages, index, family, member));
        Formula targetResolution = LimitZero(
            index, ResidualNorm(stages, index, target));
        Formula allProper = Seq(
            Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            Stage(stages, index), Sp, Neq, Sp, F.Id("top"));
        Formula allNormOne = Seq(
            Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            UniformNorm(stages, index), Sp, Eq, Sp, D(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", space), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, space), Comma,
            RowBreak, Grp(),
            stages, Colon, Sp, naturals, Sp, To, Sp, submodule, Comma, Sp,
            Open, Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            Call("HasOrthogonalProjection", Stage(stages, index)), Close, Comma,
            RowBreak, Grp(),
            family, Colon, Sp, Call("Set", space), Comma, Sp,
            target, Colon, Sp, space, Comma,
            RowBreak, Grp(),
            Open, uniform, Sp, Rightarrow, Sp, familyResolution, Close,
            Sp, Land, RowBreak, Grp(),
            Open, target, InMacro, Sp, family, Sp, Rightarrow, Sp,
            familyResolution, Sp, Rightarrow, Sp, targetResolution, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Open, allProper, Close, Sp, Rightarrow, Sp,
            Open, Open, allNormOne, Close, Sp, Land, Sp,
            Neg, Sp, uniform, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
