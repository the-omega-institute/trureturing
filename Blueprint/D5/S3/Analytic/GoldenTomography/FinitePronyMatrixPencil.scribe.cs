using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyMatrixPencilDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For separated active modes, the consecutive finite Hankel pencil is "
            + "similar to diagonal modal transport and identifies the Prony spectrum.",
        H("Finite Prony Matrix Pencil"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-modal-transport-intertwining"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_modal_transport_intertwining"),
                H("The Vandermonde observation map intertwines modal transport"),
                StatementSource.FromAuthor(IntertwiningFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For distinct Prony nodes, the square Vandermonde observation matrix is "
                            + "nonsingular. The canonical observed transport is obtained by "
                            + "conjugating diagonal multiplication by the nodes through this "
                            + "observation map.")),
                    Paragraph(Text(
                        "The displayed intertwining identity is the finite change-of-coordinates "
                            + "bridge between hidden spectral fibers and observed Hankel "
                            + "coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-hankel-pencil-equals-modal-transport"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_matrix_pencil_eq_modal_transport"),
                H("The consecutive Hankel pencil equals observed modal transport"),
                StatementSource.FromAuthor(PencilEqFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When the nodes are distinct and every modal weight is nonzero, the "
                            + "zero-shift square Hankel section is nonsingular. Its inverse "
                            + "multiplied by the one-shift section equals the canonical observed "
                            + "modal transport.")),
                    Paragraph(Text(
                        "This is the exact noiseless matrix-pencil identity. It does not select "
                            + "eigenvectors numerically or quantify sensitivity to perturbations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-matrix-pencil-charpoly"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_matrix_pencil_charpoly"),
                H("The Hankel pencil characteristic polynomial is the Prony annihilator"),
                StatementSource.FromAuthor(PencilCharpolyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The matrix pencil is similar to the diagonal matrix of Prony nodes. "
                            + "Characteristic-polynomial invariance under this conjugation gives "
                            + "the product of X - q_j, exactly the reciprocal Prony annihilator.")),
                    Paragraph(Text(
                        "Thus the exact finite Hankel pencil identifies the indexed modal nodes "
                            + "with multiplicity. No noisy root perturbation, confluent-mode "
                            + "recovery, or infinite-dimensional Koopman claim is made."))),
                DescribeRole.Theorem)),
        []));

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

    private static Formula IntertwiningFormula() => Disp(Seq(
        Call("V", F.Id("x")), Caret, Grp(F.Id("T")), Cdot,
        Call("T", F.Id("x")), Sp, Eq, Sp,
        Call("D", F.Id("x")), Cdot,
        Call("V", F.Id("x")), Caret, Grp(F.Id("T"))));

    private static Formula PencilEqFormula() => Disp(Seq(
        Call("P", F.Id("x"), F.Id("w")), Sp, Eq, Sp,
        Call("T", F.Id("x"))));

    private static Formula PencilCharpolyFormula() => Disp(Seq(
        Call("charpoly", Call("P", F.Id("x"), F.Id("w"))),
        Sp, Eq, Sp,
        Call("A", F.Id("x"))));
}
