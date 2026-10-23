using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;
internal sealed class UnificationFuelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Rewriting/UnificationFuel.";
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("unificationfuel-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite simulation of native unification", H("UnificationFuel"), Blocks(
            Paragraph(Text("The evaluator bounds recursive call depth and retains the original finite terms, substitution operations, equation order and complete error payload. Fuel exhaustion is separate from constructor failure or the occurs check. The exact simulation theorem ranges over every finite equation list and every well-formed starting substitution, with no native-only syntax restriction and no complexity bound.")),
            Paragraph(Text("The halting bound is constructed along the existing solver's verified mutual recursion. A successful equation supplies its exact proof-bearing state to the tail induction; the proof does not assume that an arbitrary raw substitution is well formed. A separate fuel induction proves persistence of every finished result. These two invariants establish exactness of the first finished execution and are consumed by the assembled search.")),
            Paragraph(Text("The theorem establishes finite halting and exact execution. Uniform computability additionally requires a coded finite representation of terms and substitutions, computability of bounded evaluation and transport to native variable ordinals. Range rejection and the ascending original-domain action projection are further obligations. These results do not establish a uniform criterion, materializer, service selector or stationary OriginalRun.")),
            Entry("one", "Bounded equation evaluation", "The one-equation evaluator follows both variable orientations, equality, occurs-check, existing aliases, fresh composed substitutions, constructor decomposition and constructor failure. Zero fuel returns none.", DescribeRole.Definition),
            Entry("core", "Bounded equation-list evaluation", "The list evaluator consumes equations in their original order, transfers successful substitutions to the tail and attaches the original equation to a propagated step error. Zero fuel returns none even for an empty list.", DescribeRole.Definition),
            Entry("run", "Terminating fuel search", "For every finite equation list and well-formed starting substitution, the search chooses the first finished fuel execution. It searches for either success or failure; it does not search for a satisfying ground assignment.", DescribeRole.Definition),
            Entry("exact_fuel_simulation", "Exact halting and returned action", "For every equation list cs and well-formed state S: there exists a bound after which every core execution equals some of the proof-erased existing Constraints.unify result; every finished core execution at any fuel already equals that result; and run cs S equals that result. Equality is of the actual substitutions and full native errors, stronger than equisatisfiability or equality of only the solution set.", DescribeRole.Theorem))));
}
