using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class HamiltonianEffectCompletionGeneratorDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hamiltonian effect orbits have the commutator derivative and span the reflector.",
        H("Hamiltonian Effect Completion Generator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hamiltonian-effect-orbit"),
                DeclarationHandle.Create(Gid + "hamiltonianEffectOrbit"),
                H("Hamiltonian effect orbit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The named orbit sends time t to the conjugate of an effect E by "
                            + "the canonical propagators at -t and t."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hamiltonian-effect-orbit-derivative-zero"),
                DeclarationHandle.Create(
                    Gid + "hamiltonian_effect_orbit_hasDerivAt_zero"),
                H("The effect orbit derivative is the commutator"),
                StatementSource.FromAuthor(DerivativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite complex matrix algebra and arbitrary matrices H "
                            + "and E, the derivative at time zero is i times H E minus E H.")),
                    Paragraph(Text(
                        "No Hermiticity or nonemptiness hypothesis is needed for this "
                            + "differentiation identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hamiltonian-effect-completion-generator"),
                DeclarationHandle.Create(Gid + "hamiltonian_effect_completion_generator"),
                H("The commutator generates the effect completion"),
                StatementSource.FromAuthor(CompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every effect has the zero-time commutator derivative, while the "
                            + "complex span of all real-time orbit points equals the supremum "
                            + "of the initial subspace under all commutator powers.")),
                    Paragraph(Text(
                        "The span equality is reused from the established analytic-flow "
                            + "generation theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-hamiltonian-effect-orbit"),
                DeclarationHandle.Create(Gid + "zero_hamiltonian_effect_orbit"),
                H("The zero Hamiltonian gives a constant orbit"),
                StatementSource.FromAuthor(ZeroHamiltonianFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The zero Hamiltonian has identity propagators, so every effect is "
                            + "fixed at every real time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-hamiltonian-effect-orbit"),
                DeclarationHandle.Create(Gid + "empty_hamiltonian_effect_orbit"),
                H("The empty-index orbit is constant"),
                StatementSource.FromAuthor(EmptyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For matrices indexed by the empty type, every orbit is the unique "
                            + "constant matrix-valued function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fin-zero-hamiltonian-effect-orbit"),
                DeclarationHandle.Create(Gid + "fin_zero_hamiltonian_effect_orbit"),
                H("The zero-dimensional orbit is constant"),
                StatementSource.FromAuthor(FinZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Fin 0 specialization records the natural-number zero-dimensional "
                            + "degeneracy explicitly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fin-one-hamiltonian-effect-orbit-derivative-zero"),
                DeclarationHandle.Create(
                    Gid + "fin_one_hamiltonian_effect_orbit_hasDerivAt_zero"),
                H("The one-dimensional derivative vanishes"),
                StatementSource.FromAuthor(FinOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "One-by-one complex matrices commute, so the commutator derivative "
                            + "vanishes at time zero."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(Formula function, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(function)), arguments);

    private static Formula ComplexNumbers() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula NaturalNumbers() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Matrices(Formula index) =>
        Call(F.Id("Matrix"), index, index, ComplexNumbers());

    private static Formula Orbit(Formula hamiltonian, Formula effect, Formula time) =>
        Call(F.Id("hamiltonianEffectOrbit"), hamiltonian, effect, time);

    private static Formula Commutator(Formula hamiltonian, Formula effect) =>
        Seq(hamiltonian, Sp, effect, Sp, Minus, Sp, effect, Sp, hamiltonian);

    private static Formula Derivative(Formula hamiltonian, Formula effect) =>
        Call(
            F.Id("deriv"),
            Call(F.Id("hamiltonianEffectOrbit"), hamiltonian, effect),
            D(0));

    private static Formula DerivativeFormula()
    {
        Formula n = F.Id("n"), hamiltonian = F.Id("H"), effect = F.Id("E");
        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, Call(F.Id("Fintype"), n), Comma, Sp,
            hamiltonian, Comma, Sp, effect, Sp, InMacro, Sp, Matrices(n), Comma, Sp,
            Derivative(hamiltonian, effect), Sp, Eq, Sp,
            F.Id("i"), Sp, Open, Commutator(hamiltonian, effect), Close, Dot));
    }

    private static Formula CompletionFormula()
    {
        Formula n = F.Id("n"), hamiltonian = F.Id("H"), effect = F.Id("E");
        Formula initial = F.Id("initial"), time = F.Id("t"), power = F.Id("k");
        Formula observable = F.Id("A"), matrices = Matrices(n);
        Formula derivativeClause = Seq(
            Forall, Sp, effect, Sp, InMacro, Sp, matrices, Comma, Sp,
            Derivative(hamiltonian, effect), Sp, Eq, Sp,
            F.Id("i"), Sp, Open, Commutator(hamiltonian, effect), Close);
        Formula orbitClause = Seq(
            Exists, Sp, time, Sp, InMacro, Sp, RealNumbers(), Comma, Sp,
            effect, Sp, InMacro, Sp, initial, Comma, Sp,
            observable, Sp, Eq, Sp, Orbit(hamiltonian, effect, time));
        Formula commutator = Call(F.Id("ad"), hamiltonian);
        Formula spanClause = Seq(
            Call(
                F.Id("span"),
                ComplexNumbers(),
                Seq(OpenBrace, observable, Sp, Bar, Sp, orbitClause, CloseBrace)),
            Sp, Eq, Sp,
            Call(
                F.Id("iSup"),
                Seq(power, Sp, InMacro, Sp, NaturalNumbers()),
                Call(F.Id("map"), initial, Seq(commutator, Caret, power))));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Comma, Sp, Call(F.Id("Fintype"), n), Comma, RowBreak, Grp(),
            hamiltonian, Sp, InMacro, Sp, matrices, Comma, Sp,
            initial, Sp, InMacro, Sp,
            Call(F.Id("Submodule"), ComplexNumbers(), matrices), Comma, RowBreak, Grp(),
            derivativeClause, Sp, Land, RowBreak, Grp(), spanClause, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ZeroHamiltonianFormula()
    {
        Formula n = F.Id("n"), effect = F.Id("E"), time = F.Id("t");
        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, Call(F.Id("Fintype"), n), Comma, Sp,
            effect, Sp, InMacro, Sp, Matrices(n), Comma, Sp,
            Forall, Sp, time, Sp, InMacro, Sp, RealNumbers(), Comma, Sp,
            Orbit(D(0), effect, time), Sp, Eq, Sp, effect, Dot));
    }

    private static Formula EmptyFormula() => ConstantOrbitFormula(F.Id("Empty"));

    private static Formula FinZeroFormula() =>
        ConstantOrbitFormula(Call(F.Id("Fin"), D(0)));

    private static Formula ConstantOrbitFormula(Formula index)
    {
        Formula hamiltonian = F.Id("H"), effect = F.Id("E"), time = F.Id("t");
        return Disp(Seq(
            Forall, Sp, hamiltonian, Comma, Sp, effect, Sp, InMacro, Sp,
            Matrices(index), Comma, Sp,
            Forall, Sp, time, Sp, InMacro, Sp, RealNumbers(), Comma, Sp,
            Orbit(hamiltonian, effect, time), Sp, Eq, Sp, effect, Dot));
    }

    private static Formula FinOneFormula()
    {
        Formula hamiltonian = F.Id("H"), effect = F.Id("E");
        Formula index = Call(F.Id("Fin"), D(1));
        return Disp(Seq(
            Forall, Sp, hamiltonian, Comma, Sp, effect, Sp, InMacro, Sp,
            Matrices(index), Comma, Sp,
            Derivative(hamiltonian, effect), Sp, Eq, Sp, D(0), Dot));
    }
}
