using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class AndrasfaiCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean labelled closed runs of the original four-state partial automaton are counted by powers of its transfer matrix, uniformly at every positive length.",
        H("Counting based labelled closed runs"),
        Blocks(
            Describe.Lean(DescribeId.Create("live-state"), DeclarationHandle.Create(Prefix + "liveState"),
                H("The live-state embedding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map liveState : Fin 4 → Fin 5 is Fin.castSucc. It sends 0,1,2,3 to the same four values in the original DFA; state 4 is the absorbing rejection state."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("closed-run"), DeclarationHandle.Create(Prefix + "ClosedRun"),
                H("Based Boolean labelled closed runs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N, ClosedRun N is the subtype of pairs (labels,q), with labels : Fin N → Bool and q : Fin 4, satisfying machine.evalFrom (liveState q) (List.ofFn labels) = liveState q. The positions and initial state are labelled; there is no quotient by rotations. Distinct Boolean labels remain distinct even when their transitions have identical source and target."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("closed-run-card-eq-trace"),
                DeclarationHandle.Create(Prefix + "closed_run_card_eq_trace"),
                H("The uniform cardinality and trace identity"), StatementSource.FromAuthor(CountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive N the rational coercion of the number of ClosedRun N equals tr(transfer^N). The transfer matrix is the original matrix with rows (1,1,0,0), (1,0,1,0), (0,0,0,1), (0,2,0,0). Its multiplicity-two entry counts both Boolean labels on the transition from state 3 to state 1. Splitting a word at its first letter and summing over live intermediate states expresses its endpoint indicator as a path-weight sum. Rejection is absorbing and contributes zero to every live endpoint. The generic integer sum_pathWeight theorem from CycleItalianDominationRecurrence identifies the resulting sum with a matrix power. Summing diagonal entries closes the runs, and matrix coefficient-map lemmas transport the integer identity to Q."))), DescribeRole.Theorem),
            Paragraph(Text("The theorem concerns actual evaluation of the existing DFA and the independently specified transfer matrix. Identifying these runs with visible subsets of an Andrasfai graph, and the graph-index-one correction, require separate counting correspondences.")))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula CountFormula()
    {
        Formula n = F.Id("N");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula rat = Seq(Mathbb, Grp(F.Id("Q")));
        Formula count = Paren(Seq(Call("card", Call("ClosedRun", n)), Sp, Colon, Sp, rat));
        Formula trace = Call("trace", new Formula.Power(Seq(Operatorname, Grp(F.Id("transfer"))), n));
        Formula equality = new Formula.Relation(count, FormulaRelationOperator.Equal, trace);
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
        return Disp(Seq(Forall, Sp, Paren(Seq(n, Sp, Colon, Sp, nat)), Comma, Sp,
            new Formula.Logic(positive, FormulaLogicOperator.Implies, equality)));
    }
}
