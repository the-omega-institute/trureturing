using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FreeEnergyFluctuationIdentityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derivatives of the free energy of a finite-dimensional Gibbs family are given by the mean energy and its fluctuation.",
        H("Free energy and energy fluctuations"),
        Blocks(
            Result("partition", "parameterizedPartitionFunction", "Parameterized partition function",
                "Scaling a fixed self-adjoint Hamiltonian by minus beta times the family parameter gives the partition function.",
                Eqn(Call("Z", F.Id("nu")), Call("partitionFunction", Seq(Grp(Seq(Minus, F.Id("beta"), F.Id("nu"))), Sp, F.Id("H")))),
                DescribeRole.Definition),
            Result("free-energy", "freeEnergy", "Free energy",
                "The free energy is minus the inverse beta times the logarithm of the partition function.",
                Eqn(Call("F", F.Id("nu")), Seq(Minus, Frac, Grp(Num(1)), Grp(F.Id("beta")), Sp, Call("log", Call("Z", F.Id("nu"))))),
                DescribeRole.Definition),
            Result("state", "equilibriumState", "Equilibrium state",
                "The equilibrium state is the existing thermal state at beta times the family parameter.",
                Eqn(Call("rho", F.Id("nu")), Call("thermalState", F.Id("H"), F.Id("beta"), F.Id("nu"))),
                DescribeRole.Definition),
            Result("first-derivative", "free_energy_deriv", "First derivative",
                "When the partition function derivative is minus beta times the partition function times the energy expectation, the free energy derivative equals the mean energy.",
                Eqn(Call("Fprime", F.Id("nu")), Call("E", F.Id("nu")))),
            Result("second-derivative", "free_energy_second_deriv", "Second derivative",
                "When the mean energy derivative is minus beta times the energy variance, the second free energy derivative is minus beta times that variance.",
                Eqn(Call("Fsecond", F.Id("nu")), Seq(Minus, F.Id("beta"), Sp, Call("Var", F.Id("nu"))))),
            Result("concavity", "free_energy_concave_at", "Concavity",
                "For positive beta, the fluctuation formula makes the second derivative nonpositive.",
                Disp(Seq(Call("Fsecond", F.Id("nu")), Sp, Le, Sp, Num(0)))))));

    private static DocumentBlock Result(string id, string declaration, string title, string prose,
        Formula formula, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("freeenergyfluct-" + id), DeclarationHandle.Create(Module + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Eqn(Formula a, Formula b) => Disp(Seq(a, Sp, Eq, Sp, b));
}
