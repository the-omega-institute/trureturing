using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class LocalObservationPartialTraceEquivalenceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete local effects distinguish exactly the reduced density state.",
        H("Local Observation Partial-Trace Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-observation-partial-trace-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence."
                        + "local_observation_partial_trace_equivalence"),
                H("Local observation equivalence is reduced-state equality"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The states are finite bipartite density matrices. The first-factor "
                            + "partial trace is constructed by summing entries with equal first "
                            + "indices.")),
                    Paragraph(Text(
                        "Equality of trace pairings against every Hermitian second-factor "
                            + "effect is equivalent to equality of the two reduced matrices."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula rho = Rho;
        Formula sigma = F.Id("sigma");
        Formula effect = F.Id("E");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrixB = Call("Matrix", b, b, complex);
        Formula densityAB = Call("DensityState", Product(a, b));
        Formula traceA(Formula state) => Call("partialTraceFirst", state);
        Formula pairing(Formula state) =>
            Call("Tr", Seq(traceA(state), Sp, effect));

        Formula assumptions = Seq(
            Call("Fintype", a), Sp, Land, Sp,
            Call("DecidableEq", a), Sp, Land, Sp,
            Call("Fintype", b), Sp, Land, Sp,
            Call("DecidableEq", b));
        Formula allEffects = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("E"),
            matrixB,
            new Formula.Logic(
                Call("Hermitian", effect),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    pairing(rho), FormulaRelationOperator.Equal, pairing(sigma))));
        Formula reducedEquality = new Formula.Relation(
            traceA(rho), FormulaRelationOperator.Equal, traceA(sigma));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("A"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("B"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("rho"), densityAB),
                new Formula.BoundVariable(FormulaIdentifier.Create("sigma"), densityAB),
            ],
            new Formula.Logic(
                assumptions,
                FormulaLogicOperator.Implies,
                new Formula.Logic(allEffects, FormulaLogicOperator.Iff, reducedEquality))));
    }
}
