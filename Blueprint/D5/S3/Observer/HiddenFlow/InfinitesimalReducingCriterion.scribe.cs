using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class InfinitesimalReducingCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generator commutation, whole Hamiltonian-flow commutation, and complementary reduction are equivalent for finite complex matrices.",
        H("Infinitesimal Reducing Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projection-commutation-is-equivalent-to-reduction"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion."
                        + "commutes_visibleProjectionMatrix_iff_reducing"),
                H("Projection commutation is equivalent to reduction"),
                StatementSource.FromAuthor(ProjectionCommutationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and R be complementary subspaces of a finite-dimensional complex "
                            + "coordinate space, and let P be the standard-basis matrix of the "
                            + "projection onto V along R. A matrix T commutes with P exactly when "
                            + "the linear operator represented by T preserves both V and R.")),
                    Paragraph(Text(
                        "Writing the complementary projection as I minus P turns commutation into "
                            + "the vanishing of both cross blocks. Those two zero blocks are "
                            + "precisely the reducing condition for the decomposition V plus R."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "generator-flow-commutation-and-flowwise-reduction-are-equivalent"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion."
                        + "infinitesimal_reducing_criterion"),
                H("Generator commutation controls reduction along the whole flow"),
                StatementSource.FromAuthor(InfinitesimalCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the Hamiltonian flow U(t) = exp(-itH), three conditions are "
                            + "equivalent: H commutes with the visible projection matrix, every "
                            + "propagator U(t) commutes with that matrix, and the complementary "
                            + "subspaces reduce the linear operator represented by U(t) for every "
                            + "real time t.")),
                    Paragraph(Text(
                        "Generator commutation passes to every exponential in the flow. Conversely, "
                            + "differentiating the flow commutation identity at time zero recovers "
                            + "commutation with the generator and hence with H after cancelling the "
                            + "nonzero scalar factor -i.")),
                    Paragraph(Text(
                        "At each time, propagator commutation is equivalent to preservation of both "
                            + "complementary blocks by the preceding projection criterion. Thus the "
                            + "infinitesimal, global-flow, and flowwise-reducing descriptions carry "
                            + "the same information."))),
                DescribeRole.Theorem))));

    private static Formula VisibleProjectionMatrix(
        Formula visible,
        Formula hidden,
        Formula witness) =>
        Call("visibleProjectionMatrix", visible, hidden, witness);

    private static Formula IsCompl(Formula visible, Formula hidden) =>
        Call("IsCompl", visible, hidden);

    private static Formula IsReducing(Formula map, Formula visible, Formula hidden) =>
        Call("IsReducing", map, visible, hidden);

    private static Formula MatrixToLinear(Formula matrix) =>
        Call("matrixToLinear", matrix);

    private static Formula HamiltonianPropagator(Formula hamiltonian, Formula time) =>
        Call("hamiltonianPropagator", hamiltonian, time);

    private static Formula ProjectionCommutationFormula()
    {
        Formula visible = F.Id("V");
        Formula hidden = F.Id("R");
        Formula witness = F.Id("h");
        Formula matrix = F.Id("T");
        Formula projection = VisibleProjectionMatrix(visible, hidden, witness);

        return Disp(Seq(
            Forall, Sp, visible, Comma, Sp, hidden, Comma, Sp,
            witness, Colon, Sp, IsCompl(visible, hidden), Comma, Sp,
            matrix, Comma, RowBreak, Grp(),
            matrix, Sp, projection, Sp, Eq, Sp, projection, Sp, matrix,
            Sp, Iff, Sp, IsReducing(MatrixToLinear(matrix), visible, hidden), Dot));
    }

    private static Formula InfinitesimalCriterionFormula()
    {
        Formula index = F.Id("n");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula vector = new Formula.TypeArrow(index, complex);
        Formula matrix = Call("Matrix", index, index, complex);
        Formula visible = F.Id("V");
        Formula hidden = F.Id("R");
        Formula witness = F.Id("h");
        Formula hamiltonian = F.Id("H");
        Formula time = F.Id("t");
        Formula projection = VisibleProjectionMatrix(visible, hidden, witness);
        Formula propagator = HamiltonianPropagator(hamiltonian, time);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, index, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Call("Fintype", index), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", index), CloseBracket, Comma, RowBreak, Grp(),
            visible, Colon, Sp, Call("Submodule", complex, vector), Comma, Sp,
            hidden, Colon, Sp, Call("Submodule", complex, vector), Comma, Sp,
            witness, Colon, Sp, IsCompl(visible, hidden), Comma, Sp,
            hamiltonian, Colon, Sp, matrix, Comma, RowBreak, Grp(),
            hamiltonian, Sp, projection, Sp, Eq, Sp, projection, Sp, hamiltonian,
            Sp, Iff, Sp, RowBreak, Grp(),
            Open, Forall, Sp, time, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            propagator, Sp, projection, Sp, Eq, Sp, projection, Sp, propagator, Close,
            Sp, Iff, Sp, RowBreak, Grp(),
            Open, Forall, Sp, time, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            IsReducing(MatrixToLinear(propagator), visible, hidden), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
