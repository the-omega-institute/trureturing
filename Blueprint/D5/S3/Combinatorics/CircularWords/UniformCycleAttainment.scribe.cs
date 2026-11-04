using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class UniformCycleAttainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fix a finite support A in an arbitrary type with decidable equality. States are all nodup oriented Cycle rotation classes with exactly support A; reflection is distinct. For at least four labels, actual labelled deletions of the same original give a history-only correct strategy with mean 2+2/(A.card-1).", H("Actual Circular Deletion Ambiguity and Attainment"), Blocks(
            Paragraph(Text("Fix a finite support A in an arbitrary type with decidable equality. States are all nodup oriented Cycle rotation classes with exactly support A; reflection is distinct. For at least four labels, actual labelled deletions of the same original give a history-only correct strategy with mean 2+2/(A.card-1).")),
            Describe.Lean(DescribeId.Create("rooted-gap-second-law"), DeclarationHandle.Create(Prefix + "rooted_gap_second_law"),
                H("Exactly the Two Cut-Adjacent Slots Collide"), StatementSource.FromAuthor(Disp(Iff(
                    Eq(Call("secondGap",F.Id("j")),Call("secondGap",F.Id("k"))),
                    Or(Eq(F.Id("j"),F.Id("k")),
                        Or(And(Eq(F.Id("j"),D(0)),Eq(F.Id("k"),D(1))),
                           And(Eq(F.Id("j"),D(1)),Eq(F.Id("k"),D(0)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Root a legal first residual at the surviving second label z, writing it z::L, with L nonempty and x fresh. Filtering z from (z::L).rotate j gives L.rotate(j-1), including j=0. Thus the actual second deletion of gapCircle(z::L,x,j) is Cycle(x::L.rotate(j-1)). Anchored injectivity and nodup rotation uniqueness show equality exactly when j=k, or j=0,k=1, or j=1,k=0. The cyclic cut is included; rooting is only a proof aid."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pair-branch-exact"), DeclarationHandle.Create(Prefix + "pair_branch_exact"),
                H("One Double Fibre and Otherwise Singletons"), StatementSource.FromAuthor(Disp(Eq(Call("NatCard",Call("doublePairLift",F.Id("A"),F.Id("x"),F.Id("z"))),D(2)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For supported distinct x,z and any legal first residual B, restrict SingleDeletionFiberCount.insertionEquiv to second-output index fibres. Its codomain PairLift is the actual subtype of nodup originals with full support A and the two specified deletion outputs. The cut-adjacent index fibre has exactly two members, and every other realized second output has exactly one. R1 also bounds every actual pair fibre by two, including unrealized outputs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ambiguous-card"), DeclarationHandle.Create(Prefix + "ambiguous_card"),
                H("Count All Originals Needing a Third Query"), StatementSource.FromAuthor(Disp(Eq(Call("card",Call("ambiguous",F.Id("A"),F.Id("x"),F.Id("z"))),Call("mul",D(2),Call("factorial",Call("sub",Call("card",F.Id("A")),D(2))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The carrier is CircularOrderCount.circles A, exactly all legal original cycles, with cardinal (A.card-1)!. Every legal first residual is realized by actual insertion. The candidateSet for a two-entry history is equivalent to PairLift. In each legal first residual exactly two originals lie in its unique double second-output fibre. Partitioning the complete carrier by first residual, whose carrier has (A.card-2)! members, gives ambiguous.card=2*(A.card-2)!. No desired count certificate is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attainingprotocol-correct"), DeclarationHandle.Create(Prefix + "attainingProtocol_correct"),
                H("A Decoder Depending Only on History"), StatementSource.FromAuthor(Disp(Eq(Call("decode",Call("run",F.Id("C"))),F.Id("C")))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Query fixed supported x,z, and stop if the actual two-observation candidateSet is a singleton. Otherwise query a fixed third supported y and stop. Require x,z,y pairwise distinct. The decoder chooses from candidates determined only by the known support and received history. ThreeSpecifiedDeletions.reconstruct_three makes the three-observation candidate set a singleton. The explicit attainingPolicy reads only the full history and its execute theorem returns exactly the same trace and that trace as terminal label with fuel four. All query outputs are deletions of the same original; neither its hidden state nor a chosen root is available to the protocol."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-cycle-attaining-mean"), DeclarationHandle.Create(Prefix + "actual_cycle_attaining_mean"),
                H("The Actual Strategy Attains the Factorial Ratio"), StatementSource.FromAuthor(Disp(Eq(Call("uniformMeanCost",F.Id("A")),Add(D(2),Div(D(2),Call("sub",Call("card",F.Id("A")),D(1))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual run length is two outside ambiguous and three inside it, so its total cost is 2*(A.card-1)!+2*(A.card-2)!. Prove the factorial recurrence (n-1)!=(n-1)*(n-2)! and positivity before rational division, distinguishing natural subtraction from subtraction in the rationals. The resulting mean is exactly 2+2/(A.card-1). The branch certificate is proved internally from the rooted law, actual insertion equivalence, and full-carrier partition."))), DescribeRole.Theorem),
            Paragraph(Text("For the full optimum, ActualCycleMeanLowerBound identifies the generic first fibre with FirstLift. With a distinct second query the generic paired set is exactly ambiguous intersected with that first fibre, and has two members; a repeated second query leaves all A.card-1 members paired. Hence TwoQueryAmbiguityCost applies to every supported adaptive full-history pointwise-terminating zero-error policy. Together with this actual correct strategy it gives the exact uniform optimum. The final binding-only conjunction is checked transiently. These observation counts do not measure readout bits, object-access cost, time, noisy recovery, or randomized protocols.")))));

    private static Formula Call(string n, params Formula[] xs) => xs.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. xs]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
}
