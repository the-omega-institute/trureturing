using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class DualAccountFullDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/DualAccountFull.";

    public DocumentDefinition Create()
    {
        Formula d = F.Id("d"), z = F.Id("Z"), x = F.Id("X");
        Formula rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula omega = Call("gibbsState", Num(0));
        Formula s = Call("vonNeumannEntropy", rho);
        Formula freedom = Call("quantumRelativeEntropy", rho, omega);
        Formula tax = Call("quantumRelativeEntropy", rho, sigma);
        Formula measured = Call("unreadState", x, rho);
        Formula assumptions = And(Call("IsRecordMeasurement", z),
            And(Call("IsRecordMeasurement", x),
                And(Call("MutuallyUnbiased", z, x),
                    And(Eqn(Call("unreadState", z, rho), rho), Eqn(measured, sigma)))));
        Formula conclusion = And(Eqn(sigma, omega),
            And(Eqn(tax, freedom),
                And(Eqn(tax, Sub(Call("log", d), s)),
                    And(Eqn(Sub(Call("vonNeumannEntropy", sigma), s), tax),
                        new Formula.Logic(Eqn(measured, rho), FormulaLogicOperator.Iff,
                            Eqn(rho, omega))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Two mutually unbiased measurements connect the full coherence tax to entropy freedom.",
            H("The full dual account"),
            Blocks(
                Paragraph(Text(
                    "The dimension d is a positive natural number. Density states are positive "
                    + "semidefinite complex matrices with trace one. Z and X are complete "
                    + "rank-one projective contexts; their projectors form record measurements. "
                    + "MutuallyUnbiased means ReTr(Z_j X_k) = 1/d for every pair of outcomes. "
                    + "unreadState denotes the sum of P_j rho P_j over a context. "
                    + "The zero-Hamiltonian Gibbs state omega is I/d. All logarithms are natural. "
                    + "Freedom means relative entropy to omega; the tax of a measurement is "
                    + "relative entropy from its input to its actual output.")),
                Describe.Lean(
                    DescribeId.Create("dual-account-full"),
                    DeclarationHandle.Create(Owner + "dual_account_full"),
                    H("A Z-fixed state pays its full freedom in X"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("d", F.Id("PositiveNatural")),
                            Bound("Z", Call("RankOneContext", d)),
                            Bound("X", Call("RankOneContext", d)),
                            Bound("rho", Call("DensityState", d)),
                            Bound("sigma", Call("DensityState", d))],
                        new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Mutual unbiasedness makes the composition of the two measurements "
                        + "completely depolarizing. Since Z already fixes rho, the actual X "
                        + "output sigma must be omega. The Gibbs entropy identity then makes "
                        + "the X tax equal to log(d) minus the input entropy, and to the entropy "
                        + "gained in that measurement. If X also fixes rho, rho itself is omega; "
                        + "the converse follows from the same output equality. The proof also "
                        + "covers dimension one, where trace normalization fixes "
                        + "the only entry."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("entropy-freedom-segment"),
                    DeclarationHandle.Create(Owner + "entropy_freedom_segment"),
                    H("Every state lies on the entropy and freedom segment"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("d", F.Id("PositiveNatural")),
                            Bound("rho", Call("DensityState", d))],
                        And(Le(Num(0), s), And(Le(Num(0), freedom),
                            Eqn(Add(s, freedom), Call("log", d))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The eigenvalues of a density state form a probability distribution, "
                        + "and its von Neumann entropy is their Shannon entropy. The finite "
                        + "entropy bounds give zero at the lower end and log(d) at the upper "
                        + "end. The Gibbs identity supplies the complementary freedom. Thus "
                        + "any trajectory of density states lies on this segment point by point; "
                        + "no dynamical law or parametrization of time is assumed."))),
                    DescribeRole.Theorem))));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
