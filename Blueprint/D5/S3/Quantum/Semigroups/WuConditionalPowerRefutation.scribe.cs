using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuConditionalPowerRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuConditionalPowerRefutation.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful qubit ancilla refutes the conditional power inequality at s=2.",
        H("The two-mode conditional power inequality fails at s=2"),
        Blocks(
            Paragraph(Text("Let Q = Fin 2 and S = Q × Q. The ancillary index is another copy of Q. "
                + "With β = log 4, write D = diag(1,4)/5, Dphys = D ⊗ D, and τ = diag(1,1024)/1025. "
                + "The reference is Σ = Dphys ⊗ τ. With e = |0⟩⟨1| and Z = diag(−1,1), the two signed jumps are e ⊗ I and Z ⊗ e. "
                + "Each is amplified by the ancillary identity. In the convention T(t) = exp(−tL), each amplified J contributes "
                + "(2/5)K(J) + (8/5)K(J†), where K(J)(Y) = (J†JY + YJ†J)/2 − J†YJ.")),
            Paragraph(Text("Set P = Σ^(1/4), M = PXP and F = M². Write E(X) for Re Tr[M P L(X) P] "
                + "and H(X) for Re Tr[F(log F − log(Dphys ⊗ Tr_S F))]. The marginal traces out both physical qubits. "
                + "At s = 2, Wu's (3.55) at β = log 4 gives α = 1/(3 log 2).")),
            Describe.Lean(DescribeId.Create("wu-conditional-power-claim"),
                DeclarationHandle.Create(Owner + "claim"), H("The conditional extension"),
                StatementSource.FromAuthor(Disp(ClaimFormula())), AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("The proposed conditional extension of Wu's (3.54) requires the bound for every positive definite complex matrix X on S × Q."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wu-conditional-power-result"),
                DeclarationHandle.Create(Owner + "result"), H("A faithful counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Take X = I ⊗ X₄, where in right-qubit and ancilla order 00,01,10,11 the diagonal of X₄ is "
                        + "(1,1,1/128,1). Its only off-diagonal entries are the symmetric 00,11 pair, each 1/8. "
                        + "The left dissipator vanishes on this algebra. The signs of the right jump multiply to one there.")),
                    Paragraph(Text("For A = 1/5125, the actual marginal is A diag(8193/4096,5121). The energy is (36609/10240)A "
                        + "and H(X) > 11 A log 2. The paired block in the power on the right qubit and ancilla has "
                        + "diagonals 2A and 4097A and coherence 65A. Its eigenvalues are A(2−δ) and A(4097+δ), "
                        + "where δ(4095+δ) = 65² and 1 < δ < 2. The two scalar supporting lines for x log x give "
                        + "a strict gain exceeding 11 A log 2 over the diagonal. "
                        + "The diagonal relative entropy is nonnegative by the scalar logarithm bound and equal trace. "
                        + "Tensoring with the left density preserves the conditional entropy by cancellation of the logarithmic scale in each left block.")),
                    Paragraph(Text("The deficit E(X) − αH(X) is strictly below −A/15. The partial transpose of X has a principal "
                        + "minor of determinant −1/128 at left occupation zero. The power also has a negative partial-transpose minor. "
                        + "The power and its conditional reference are positive definite."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        var x = F.Id("X");
        var qubit = Call("Fin", D(2));
        var index = Seq(Open, qubit, Sp, F.Times, Sp, qubit, Close, Sp, F.Times, Sp, qubit);
        var matrices = Call("Matrix", index, index, Seq(Mathbb, Grp(F.Id("C"))));
        var inequality = new Formula.Relation(
            new Formula.Binary(Named("alpha"), FormulaBinaryOperator.Multiply, Call("H", x)),
            FormulaRelationOperator.LessThanOrEqual, Call("E", x));
        var implication = new Formula.Logic(Call("PosDef", x), FormulaLogicOperator.Implies, inequality);
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("X"), matrices, implication);
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
}
