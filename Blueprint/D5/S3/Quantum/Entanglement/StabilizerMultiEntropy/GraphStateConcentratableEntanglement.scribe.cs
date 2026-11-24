using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class GraphStateConcentratableEntanglementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For normalized graph states, generalized concentratable entanglement is monotone under subsystem inclusion at every real order greater than one.",
        H("Subsystem monotonicity of generalized concentratable entanglement for graph states"),
        Blocks(
            Paragraph(Text("The graph is any symmetric binary adjacency matrix with zero diagonal. "
                + "The state has computational coefficients 2^(-N/2) times the sign of the graph's ordered binary quadratic phase. "
                + "The matrix reduction uses the original coefficients and sums exactly over each omitted binary configuration.")),
            Describe.Lean(DescribeId.Create("graph-state-gce-monotonicity"),
                DeclarationHandle.Create(Prefix + "physical_graph_gce_monotone"),
                H("Exact cut-rank moments and subsystem monotonicity"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For a subset U of the qubits, r(U) is the binary rank of the rectangular adjacency block from U to its complement. "
                        + "Summing the characters of the omitted bit strings shows that the original reduced density matrix is a trace-one positive multiple of a projector; "
                        + "the real functional calculus gives its exact moment for arbitrary real K > 1. "
                        + "The proof of cut-rank submodularity uses supported subspaces and the dimension identity for their sum and intersection.")),
                    Paragraph(Text("Complement symmetry and the Ahlswede–Daykin four-functions theorem show the average of these moments decreases under inclusion. "
                        + "Subtracting it from one and dividing by K - 1 gives the stated increase. "
                        + "This is a positive graph-state class for the measure in Liu, Knörzer, Wang and Tura; it does not overturn the repository's four-qubit refutation "
                        + "for arbitrary pure states or assert an arbitrary stabilizer-state physical transport theorem."))),
                DescribeRole.Theorem))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));

    private static Formula Statement()
    {
        var n = F.Id("N");
        var a = F.Id("A");
        var k = F.Id("K");
        var u = F.Id("U");
        var sites = Call("Fin", n);
        var r = Call("cutRank", a, u);
        var exponent = new Formula.Binary(
            new Formula.Binary(Num(1), FormulaBinaryOperator.Subtract, k),
            FormulaBinaryOperator.Multiply, r);
        var moment = Equal(Call("TrPower", a, k, u), new Formula.Power(Num(2), exponent));
        var everyU = All("U", Call("Subsets", sites), moment);
        var hypotheses = And(Call("Symmetric", a), And(Call("ZeroDiagonal", a),
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, k)));
        var conclusion = And(everyU, Call("Monotone", Call("GCE", a, k)));
        var law = new Formula.Logic(P(hypotheses), FormulaLogicOperator.Implies, P(conclusion));
        return Disp(All("N", Seq(Mathbb, Grp(F.Id("N"))),
            All("K", Seq(Mathbb, Grp(F.Id("R"))), All("A", Call("BinaryMatrices", sites), law))));
    }
}
