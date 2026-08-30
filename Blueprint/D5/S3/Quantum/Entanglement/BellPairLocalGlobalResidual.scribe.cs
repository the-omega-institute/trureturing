using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class BellPairLocalGlobalResidualDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal Bell pure states have identical complete local marginals.",
        H("An Orthogonal Bell Pair in the Local-Global Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("negative-bell-coefficients"),
                DeclarationHandle.Create(DeclarationPrefix + "bellMinusCoefficients"),
                H("Negative-phase Bell coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named two-by-two coefficient matrix has entries one and minus one "
                        + "on the diagonal and zero off the diagonal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-bell-vector"),
                DeclarationHandle.Create(DeclarationPrefix + "bellMinusVector"),
                H("Negative-phase Bell vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Dividing the named coefficient matrix by the square root of two gives "
                        + "the vector represented by 00 minus 11."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-bell-density"),
                DeclarationHandle.Create(DeclarationPrefix + "bellMinusDensity"),
                H("Negative-phase Bell density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The outer product of the negative-phase Bell vector with its adjoint "
                        + "is its named rank-one density matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-qubit-local-global-residual"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "twoQubitLocalGlobalResidual"),
                H("Two-qubit local-global residual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the two-factor instance of the source definition. It consists "
                        + "of distinct positive trace-one matrices whose two canonical "
                        + "partial traces agree."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orthogonal-bell-pair-residual-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "bell_pair_local_global_residual"),
                H("The orthogonal Bell pair is locally indistinguishable"),
                StatementSource.FromAuthor(BellPairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The imported positive-phase witness supplies positivity, trace one, "
                            + "rank one, and both local marginals for the first state.")),
                    Paragraph(Text(
                        "Direct finite calculations give the same data for the negative-phase "
                            + "state. Their off-diagonal density entries differ, while the "
                            + "inner product of the defining vectors is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-qubit-residual-nonempty"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "two_qubit_local_global_residual_nonempty"),
                H("Complete local data do not determine the global state"),
                StatementSource.FromAuthor(NonemptyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive- and negative-phase Bell densities give an explicit member "
                        + "of the two-qubit local-global residual."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-pairs-excluded"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "diagonal_pair_not_mem_two_qubit_local_global_residual"),
                H("Degenerate equal pairs are excluded"),
                StatementSource.FromAuthor(DegenerateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every self-pair is excluded by global distinctness. In particular, this "
                        + "covers the zero pair, identity pair, and every constant self-pair."))),
                DescribeRole.Theorem))));

    private static Formula BellPairFormula()
    {
        Formula plusDensity = F.Id("rhoPlus");
        Formula minusDensity = F.Id("rhoMinus");
        Formula plusVector = F.Id("PhiPlus");
        Formula minusVector = F.Id("PhiMinus");
        Formula pair = Seq(Open, plusDensity, Comma, Sp, minusDensity, Close);

        return Disp(Seq(
            pair, Sp, InMacro, Sp, F.Id("QLGRes2"), Sp, Land, RowBreak, Grp(),
            Call("rank", plusDensity), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Call("rank", minusDensity), Sp, Eq, Sp, D(1), Sp, Land, RowBreak, Grp(),
            Call("inner", plusVector, minusVector), Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula NonemptyFormula() =>
        Disp(Seq(F.Id("QLGRes2"), Sp, Neq, Sp, Emptyset, Dot));

    private static Formula DegenerateFormula()
    {
        Formula density = Rho;
        Formula pair = Seq(Open, density, Comma, Sp, density, Close);

        return Disp(Seq(
            Forall, Sp, density, Comma, Sp,
            Neg, Sp, Grp(Seq(pair, Sp, InMacro, Sp, F.Id("QLGRes2"))), Dot));
    }
}
