using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class AnalyticFlowGenerationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional Hamiltonian flow spans its nested commutator closure.",
        H("Analytic Flow Generation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("analytic-flow-generates-commutator-closure"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/AnalyticFlowGeneration."
                        + "analytic_flow_generates_commutator_closure"),
                H("Hamiltonian flow generates the commutator closure"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a finite complex matrix and let initial be a complex "
                            + "subspace of observables. The orbit is constructed from the "
                            + "canonical Hamiltonian propagator, with no chosen basis or "
                            + "auxiliary closure object.")),
                    Paragraph(Text(
                        "The complex span of all real-time conjugates of initial equals the "
                            + "supremum of its images under every power of the canonical "
                            + "left-minus-right multiplication endomorphism.")),
                    Paragraph(Text(
                        "Finite dimensionality makes the generated subspaces closed. Difference "
                            + "quotients recover the commutator generator from the flow, while "
                            + "the exponential series and uniqueness for the linear ordinary "
                            + "differential equation recover every flow point from the power "
                            + "orbit."))),
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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula hamiltonian = F.Id("H");
        Formula initial = F.Id("initial");
        Formula observable = F.Id("A");
        Formula seed = F.Id("E");
        Formula time = F.Id("t");
        Formula power = F.Id("k");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula matrices = Call("Matrix", n, n, complex);
        Formula propagator(Formula at) => Call("hamiltonianPropagator", hamiltonian, at);
        Formula conjugate = Seq(
            propagator(Seq(Minus, time)), Sp, seed, Sp, propagator(time));
        Formula orbit = Seq(
            Open, Exists, Sp, time, InMacro, Sp, real, Comma, Sp,
            seed, InMacro, Sp, initial, Comma, Sp,
            observable, Sp, Eq, Sp, conjugate, Close);
        Formula commutator = Seq(
            Call("mulLeft", complex, hamiltonian), Sp, Minus, Sp,
            Call("mulRight", complex, hamiltonian));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Call("Fintype", n), Comma, Sp, Call("DecidableEq", n), Comma, RowBreak, Grp(),
            hamiltonian, Colon, Sp, matrices, Comma, Sp,
            initial, Colon, Sp, Call("Submodule", complex, matrices), Comma, RowBreak, Grp(),
            Call("span", complex, Seq(OpenBrace, observable, Sp, Bar, Sp, orbit, CloseBrace)),
            Sp, Eq, Sp,
            Call("iSup", Seq(power, Sp, InMacro, Sp, natural),
                Call("map", initial, Seq(Open, commutator, Close, Caret, power))),
            Dot, End, Grp(F.Id("gathered"))));
    }
}
