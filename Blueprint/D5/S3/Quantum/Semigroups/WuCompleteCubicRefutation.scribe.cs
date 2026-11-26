using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCompleteCubicRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful separable two-qubit state refutes the fixed-marginal tracial cubic bound.",
        H("The fixed-marginal cubic bound fails for a separable state"),
        Blocks(
            Paragraph(Text("Use the product basis 00, 01, 10, 11 with the system index first. "
                + "Write R_A = Tr_B R and R_B = Tr_A R, D = I₂/2, σ = diag(2,26)/28, and T = D ⊗ R_B. "
                + "The amplified jump is J = |0⟩⟨1| ⊗ I₂. With a = b = 1/2 the paired generator is "
                + "L(Y) = 2a K(J,Y) + 2b K(J†,Y), where K(V,Y) = (V†VY + YV†V)/2 − V†YV.")),
            Paragraph(Text("In the ordinary-trace convention of Wu v1 (2.4), take s = 3 and its conjugate "
                + "s′ = 3/2. Put p = 1/3, q = 2/3, and X_r = T^(−r/2) R^r T^(−r/2). "
                + "Then E(R) = Re Tr[T^(1/2) X_q T^(1/2) L(X_p)]/(4pq) and "
                + "H(R) = Re Tr[R(log R − log T)].")),
            Describe.Lean(DescribeId.Create("wu-complete-cubic-claim"),
                DeclarationHandle.Create(Owner + "claim"), H("Proposed fixed-marginal extension"),
                StatementSource.FromAuthor(Disp(ClaimFormula())), AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("This research claim proposes the ancillary extension of Wu v1 (3.54) "
                    + "with the sharp tracial coefficient 1/2 from (3.55) at β = 0. The joint state is faithful "
                    + "and separable across the system and ancilla, with R_A = D and R_B = σ. These marginals enforce trace one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wu-complete-cubic-result"),
                DeclarationHandle.Create(Owner + "result"), H("A faithful separable counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Take ρ with diagonal (2,26,2,26)/56 and symmetric 00,11 entries 5/56. "
                        + "All other off-diagonal entries vanish. Its spectrum is (1,26,2,27)/56 and its "
                        + "actual marginals are D and σ. It is a mixture of D ⊗ D with weight 4/56 and "
                        + "four rank-one product projectors with weight 13/56 each. Their local unit vectors are "
                        + "(1,z)/√2 and (1,5 overline(z))/√26 for z = 1, −1, i, −i.")),
                    Paragraph(Text("The actual T commutes with J, so both T and I satisfy the modular relation "
                        + "with rate ratio a/b = 1. The spectral expansion in generatorTrace_eq_cosh uses the same "
                        + "eigenvalues of ρ, jump entries in its eigenbasis, and rates for both references. "
                        + "The embedded traces are therefore equal, so the energy can be evaluated with I. "
                        + "The entropy uses the actual T.")),
                    Paragraph(Text("For x = 2^(1/3) and y = 26^(1/3), the finite certificate gives "
                        + "56 E(ρ) = (9/8)[56 − (14x² + 17x + 38y² + 113y)/13] and "
                        + "56 H(ρ) = 27 log 27 − 2 log 2 − 26 log 26. "
                        + "The rational cube-root bounds x > 12599/10000 and y > 29624/10000 and "
                        + "the log-series bounds log(3/2) ≥ 2/5, log 2 ≥ 56/81, and log(27/26) ≥ 2/53 "
                        + "give 56 E(ρ) < 7/5 < 28 H(ρ)."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        var r = F.Id("R");
        var index = Call("Fin", D(4));
        var matrices = Call("Matrix", index, index, Seq(Mathbb, Grp(F.Id("C"))));
        var systemTrace = new Formula.Apply(new Formula.Subscript(Named("Tr"), F.Id("B")), [r]);
        var ancillaTrace = new Formula.Apply(new Formula.Subscript(Named("Tr"), F.Id("A")), [r]);
        var systemMarginal = new Formula.Relation(systemTrace, FormulaRelationOperator.Equal, F.Id("D"));
        var ancillaMarginal = new Formula.Relation(ancillaTrace, FormulaRelationOperator.Equal, SigmaLower);
        var inequality = new Formula.Relation(
            new Formula.Fraction(Call("H", r), D(2)), FormulaRelationOperator.LessThanOrEqual, Call("E", r));
        var implication = new Formula.Logic(Call("PosDef", r), FormulaLogicOperator.Implies,
            new Formula.Logic(systemMarginal, FormulaLogicOperator.Implies,
                new Formula.Logic(ancillaMarginal, FormulaLogicOperator.Implies,
                    new Formula.Logic(Call("Separable", r), FormulaLogicOperator.Implies, inequality))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("R"), matrices, implication);
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
}
