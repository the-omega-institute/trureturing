using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class CoordinateFibreCountsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts";

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type,
        Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);

    private static Formula Some(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ParityAndBound(Formula m, Formula z) =>
        And(Seq(z, Sp, Le, Sp, m), Seq(Call("ModTwo", z), Sp, Eq, Sp, Call("ModTwo", m)));

    private static Formula WithOrbitData(Formula i, Formula t, Formula body, bool existential)
    {
        var sizes = Call("OrbitSizes", i, t);
        var fixedCounts = Call("OrbitCoordinateCounts", i, t);
        return existential
            ? Some("m", sizes, Some("z", fixedCounts, body))
            : All("m", sizes, All("z", fixedCounts, body));
    }

    private static Formula Extraction()
    {
        var i = F.Id("I");
        var t = F.Id("T");
        var f = F.Id("f");
        var m = F.Id("m");
        var z = F.Id("z");
        var orbit = F.Id("o");
        var coordinate = F.Id("j");
        var bounds = All("o", Call("Orbits", i, t), All("j", i,
            ParityAndBound(Call("m", orbit), Call("z", orbit, coordinate))));
        var data = WithOrbitData(i, t, And(bounds, Call("FibreEquations", f, m, z)), true);
        return Disp(All("I", F.Id("FiniteIndexTypes"), All("T", Call("ActionTypes", i),
            All("f", Call("FiniteEquivariantReadouts", i, t), data))));
    }

    private static Formula Exact()
    {
        var i = F.Id("I");
        var t = F.Id("T");
        var f = F.Id("f");
        var m = F.Id("m");
        var z = F.Id("z");
        var target = F.Id("x");
        var coordinate = F.Id("j");
        var orbit = Call("Orbit", target);
        var exists = Some("f", Call("FiniteEquivariantReadouts", i, t),
            Call("FibreEquations", f, m, z));
        var bound = All("x", t, All("j", i, Implies(Call("Fixes", coordinate, target),
            ParityAndBound(Call("m", orbit), Call("z", orbit, coordinate)))));
        return Disp(All("I", F.Id("FiniteIndexTypes"), All("T", Call("FiniteActionTypes", i),
            WithOrbitData(i, t, Iff(exists, bound), false))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate fixed counts on finite fibres of an equivariant readout.",
        H("Fixed-seed counts over output orbits"),
        Blocks(
            Describe.Lean(DescribeId.Create("extract-orbit-fibre-counts"),
                DeclarationHandle.Create(Module + ".orbit_fixed_fibre_counts"),
                H("Fibre sizes and fixed counts are constant on each output orbit"),
                StatementSource.FromAuthor(Extraction()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The action group for an index type I is the product of copies of "
                        + "the group of order two, with one generator per index. An action type T "
                        + "carries an action of this group. A finite equivariant readout consists "
                        + "of a finite source with an action and a map f commuting with the actions.")),
                    Paragraph(Text("The fibre equations say that each output x has m(Orbit(x)) "
                        + "preimages. For coordinate j, the number of those preimages fixed by "
                        + "its generator is z(Orbit(x),j) if the generator fixes x, and zero "
                        + "otherwise. OrbitSizes and OrbitCoordinateCounts are natural-valued "
                        + "functions on orbits and on orbit-coordinate pairs, respectively.")),
                    Paragraph(Text("Translating a fibre preserves its size and its fixed counts, "
                        + "since the group is abelian. When a generator fixes x, it acts as an "
                        + "involution on the fibre, so the moved seeds occur in pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("realize-exact-orbit-fibre-counts"),
                DeclarationHandle.Create(Module + ".exact_orbit_fibre_counts"),
                H("The size and parity conditions characterize common realizations"),
                StatementSource.FromAuthor(Exact()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take a finite output action type T, a nonnegative fibre "
                        + "size m on each orbit and a nonnegative fixed count z per orbit and "
                        + "coordinate. The fibre equations have a common finite equivariant "
                        + "realization exactly when each generator that fixes the output satisfies "
                        + "the displayed size and parity conditions.")),
                    Paragraph(Text("Above each output, take a common set of paired labels for its "
                        + "orbit and a singleton label if the fibre size is odd. Each coordinate "
                        + "generator swaps the necessary number of label pairs independently. "
                        + "The permutations commute because they act pair by pair. The group "
                        + "simultaneously acts on the underlying output and on these labels."))),
                DescribeRole.Theorem))));
}
