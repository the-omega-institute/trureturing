using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class VectorShellEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete orthogonal Hilbert sum decomposes vector energy into initial, "
            + "countable-shell, and residual weights.",
        H("Vector Shell Energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-orthogonal-shells-decompose-vector-energy"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/VectorShellEnergy."
                        + "vector_shell_energy_decomposition"),
                H("Complete orthogonal shells decompose vector energy"),
                StatementSource.FromAuthor(EnergyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a complete real inner-product space presented as an internal "
                            + "Hilbert sum with two distinguished coordinates and a countable "
                            + "family of extracted-shell coordinates. The distinguished "
                            + "coordinates represent the initial and residual subspaces.")),
                    Paragraph(Text(
                        "For a vector psi, initialComponent, extractedComponent, and "
                            + "residualComponent embed its Hilbert-sum coordinates back into H. "
                            + "The extracted index n equals zero for the source shell numbered "
                            + "one, so the displayed sum is the exact reindexing of shells n at "
                            + "least one.")),
                    Paragraph(Text(
                        "The squared norm equals the initial squared norm, the infinite sum of "
                            + "extracted squared norms, and the residual squared norm. The same "
                            + "named theorem retains the unit-vector clause: when the vector norm "
                            + "is one, these nonnegative weights have total mass one.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies lp.norm_rpow_eq_tsum and the canonical isometric "
                            + "equivalence associated with IsHilbertSum; the proof applies them "
                            + "directly. Repository search found finite-stage and one-step shell "
                            + "identities, but no equal infinite energy-and-probability theorem."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Norm(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert);

    private static Formula NormSquared(Formula value) =>
        Seq(Norm(value), Caret, Grp(D(2)));

    private static Formula EnergyFormula()
    {
        Formula space = F.Id("H");
        Formula family = F.Id("G");
        Formula embedding = F.Id("V");
        Formula decomposition = F.Id("hV");
        Formula vector = Psi;
        Formula n = F.Id("n");
        Formula initial = NormSquared(Call(
            "initialComponent", embedding, decomposition, vector));
        Formula shell = NormSquared(Call(
            "extractedComponent", embedding, decomposition, n, vector));
        Formula residual = NormSquared(Call(
            "residualComponent", embedding, decomposition, vector));
        Formula shellSum = Seq(
            Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(Infty), Sp, shell);
        Formula total = Seq(initial, Sp, Plus, Sp, shellSum, Sp, Plus, Sp, residual);

        return Disp(Seq(
            Forall, Sp, space, Comma, Sp, family, Comma, Sp, embedding, Comma, Sp,
            decomposition, Comma, Sp, vector, Comma, Esc,
            Call("IsHilbertSum", space, family, embedding, decomposition), Sp,
            Rightarrow, RowBreak,
            NormSquared(vector), Sp, Eq, Sp, total, Sp, Land, RowBreak,
            Open, Norm(vector), Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            D(0), Sp, Leq, Sp, initial, Sp, Land, Sp,
            Open, Forall, Sp, n, Comma, Esc, D(0), Sp, Leq, Sp, shell, Close,
            Sp, Land, RowBreak,
            D(0), Sp, Leq, Sp, residual, Sp, Land, Sp,
            total, Sp, Eq, Sp, D(1), Close, Dot));
    }
}
