using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityMinimumSeedSpectrumDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var z = F.Id("z");
        return Disp(All("n", F.Id("Nat"), All("z", Call("CountVectors", n),
            new Formula.Logic(Call("RealizedAtMinimum", n, z), FormulaLogicOperator.Iff,
                Call("EvenCutCounts", n, z)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The smallest uniform seed budget has an exact coordinate fixed-count spectrum.",
        H("Fixed counts at the least coloured parity budget"),
        Blocks(Describe.Lean(DescribeId.Create("parity-minimum-budget-exact-fixed-counts"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityMinimumSeedSpectrum.exact_minimal_budget_fixed_counts"),
            H("The even-word cuts at the least positive seed budget"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("CountVectors(n) consists of the natural-valued functions on Fin(n+2). " +
                    "RealizedAtMinimum(n,z) means an equally weighted seed set of size 2^(n+3) with " +
                    "equivariant readouts to the two uniformly distributed coloured parity classes " +
                    "has exactly z(i) seeds fixed by the subgroup acting at coordinate i.")),
                Paragraph(Text("Let M = 2^n. EvenCutCounts(n,z) means there is an integer vector a with " +
                    "0 <= a(i) <= M and z(i) = 4(M-a(i)) at every coordinate. For every even binary " +
                    "word e, the sum of a(i) at its zero coordinates and M-a(i) at its one " +
                    "coordinates is at least M.")),
                Paragraph(Text("Each coloured marginal fibre contains two seeds. If two seeds share " +
                    "both outputs, they fill both fibres. Equivariance then forces both outputs " +
                    "to have the same stabilizer. A coordinate at which the two parity profiles " +
                    "differ has a generator that fixes just one output.")),
                Paragraph(Text("The joint readout is injective, so equivariance identifies fixed seeds " +
                    "with seeds over fixed output pairs. The normalized mismatch vector gives the " +
                    "cuts and the common-one counts. Conversely, a coupling furnished by the cuts " +
                    "lifts to an equivariant seed action by taking the four colour combinations."))),
            DescribeRole.Theorem))));
}
