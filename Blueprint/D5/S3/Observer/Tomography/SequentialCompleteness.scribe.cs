using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class SequentialCompletenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sequential readout completeness is equivalent to a trivial residual and full visible span.",
        H("Sequential Completeness"),
        Blocks(Describe.Lean(
            DescribeId.Create("sequential-readout-completeness-three-way"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Tomography/SequentialCompleteness."
                    + "sequential_completeness_criterion"),
            H("Sequential completeness, zero residual, and full visible span"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The allowed readout effects are centered Hermitian directions. Their "
                        + "real span is combined with the scalar identity line to construct "
                        + "the visible Hermitian space, and the residual is its orthogonal "
                        + "complement.")),
                Paragraph(Text(
                    "The canonical density-state signature is injective exactly when the "
                        + "centered effect span is full; finite-dimensional orthogonality "
                        + "then identifies a zero residual with a full visible span."))),
            DescribeRole.Theorem))));

    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), indexType = F.Id("A"), effects = F.Id("E");
        Formula index = F.Id("i"), rho = Rho;
        Formula hermitian = Seq(
            Operatorname, Grp(F.Id("Herm")), Underscore, Grp(d));
        Formula traceZero = Seq(hermitian, Caret, Grp(D(0)));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula centeredVisible = Sub(F.Id("V"), D(0));
        Formula visible = F.Id("V"), residual = F.Id("N");
        Formula effect = Sub(effects, index);
        Formula stateType = Call(F.Id("DensityState"), Call(F.Id("Fin"), d));
        Formula signature = Seq(
            Open, rho, Colon, Sp, stateType, Sp, Mapsto, Sp,
            Open, index, Colon, Sp, indexType, Sp, Mapsto, Sp,
            Re, Sp, Call(F.Id("Tr"), Seq(Call(F.Id("matrix"), rho), Sp, effect)), Close,
            Close);

        Formula definitions = Seq(
            centeredVisible, Sp, Eq, Sp,
            Call(F.Id("span"), Seq(reals, Comma, Sp,
                Open, effect, Colon, Sp, index, InMacro, Sp, indexType, Close)),
            Comma, Sp,
            visible, Sp, Eq, Sp, reals, F.Id("I"), Sp, Plus, Sp, centeredVisible,
            Comma, RowBreak,
            Grp(), residual, Sp, Eq, Sp,
            visible, Caret, Grp(Perp));

        return Disp(Seq(
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call(Seq(Operatorname, Grp(F.Id("NeZero"))), d), Comma, Sp,
            indexType, Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, RowBreak,
            Grp(), effects, Colon, Sp, indexType, Sp, To, Sp, traceZero, Comma, RowBreak,
            Grp(), definitions, Comma, RowBreak,
            Grp(), Call(Seq(Operatorname, Grp(F.Id("Injective"))), signature), Sp, Iff, Sp,
            residual, Sp, Eq, Sp, OpenBrace, D(0), CloseBrace, Sp, Iff, Sp,
            visible, Sp, Eq, Sp, hermitian, Dot));
    }
}
