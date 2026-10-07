using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualObserverPairReachDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least absorbing paired response relation is characterized by equal coarse words and exactly characterizes coarse action factorization on every finite raw history.",
        H("Absorbing Paired Histories and Coarse Action Factorization"),
        Blocks(
            Paragraph(Text("M is any complete finite nominal observer, with initial row e0 and action in Sum Address Bool. The existing barStep follows the raw transition at a query row and fixes a halt row for every reply. responseState folds this absorbing step from a specified row; historyAction folds the replies from e0 and returns the resulting action. No source, cache truth, legal execution, termination, fuel or acyclicity assumption is imposed.")),
            Def("PairReach", "Least synchronized raw-response relation", "PairReach starts at (e0,e0). From any generated pair (e,f), every raw pair (y,z) with kappa(y)=kappa(z) generates (barStep(M,e,y),barStep(M,f,z)). All four replies remain available, and absent and branch may be paired. Edges remain available after either component has halted."),
            Def("pairActionInvariant", "Paired action equality", "At every generated pair the two actions agree. This concerns action equality rather than state equality."),
            Def("coarseResponseWord", "Coarse response words", "Map the existing kappa over a raw reply word. Alpha and beta retain their distinct Boolean leaf labels; absent and branch both map to none. Address labels are not part of a response word."),
            Describe.Lean(DescribeId.Create("observer-pair-reach-response-words"), DeclarationHandle.Create(Prefix + "pairReach_response_words"),
                H("Equal-coarse words extend a generated pair"), StatementSource.FromAuthor(ExtensionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any generated starting pair, folding any two finite raw words with equal coarse images yields another generated pair. Induction matches their coarse-equal heads and applies the generating step before processing their tails. The same statement applies to words continuing beyond a halt."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("observer-pair-reach-word-characterization"), DeclarationHandle.Create(Prefix + "pairReach_iff_equal_coarse_response_words"),
                H("Exact equal-coarse response-word characterization"), StatementSource.FromAuthor(CharacterizationFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A generated pair is exactly a pair of folds from e0 of two finite raw words having equal coarse images. Induction on the generated relation appends the edge replies to the two words. In the reverse direction, the equal-coarse word extension applied to the initial pair constructs the required pair. Raw words need not be equal, and their final rows need not be equal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("observer-pair-reach-all-history-factorization"), DeclarationHandle.Create(Prefix + "pairActionInvariant_iff_allHistoryFactorization"),
                H("Exact all-history factorization with absorbing stops"), StatementSource.FromAuthor(FactorizationFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Paired action equality holds exactly when Function.FactorsThrough(historyAction(M),kappa_hist) holds. FactorsThrough means equal actions whenever the complete coarse histories agree. The existing kappa_hist retains addresses, order and repetitions. Its domain is every finite RawHistory, including unreachable, impossible, wrong-address, duplicate and raw-inconsistent labels.")),
                    Paragraph(Text("Projecting equal coarse histories to their replies supplies equal-coarse response words, so the characterization gives the forward implication. Conversely, encode the two response words with the same fixed empty literal address at every position. Their coarse histories agree, and all-history factorization gives action equality at the represented pair. No actual-source condition restricts these encodings. Absorbing barStep permits arbitrary replies after either halt. These statements concern the original observer and assert no transformed execution, cache projection or cost bound."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("observer-pair-reach-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula All(string names, Formula f) => Seq(Forall, Sp,
        Seq(names.Split(',').Select((name, i) => i == 0 ? V(name) : Seq(Comma, Sp, V(name))).ToArray()), Comma, Sp, Par(f));
    private static Formula Some(string names, Formula f) => Seq(Exists, Sp,
        Seq(names.Split(',').Select((name, i) => i == 0 ? V(name) : Seq(Comma, Sp, V(name))).ToArray()), Comma, Sp, Par(f));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Coarse(Formula w) => Call("map", V("kappa"), w);
    private static Formula State(Formula e, Formula w) => Call("responseState", V("M"), e, w);
    private static Formula Reach(Formula e, Formula f) => Call("PairReach", V("M"), e, f);
    private static Formula ExtensionFormula()
    {
        Formula same = EqOf(Coarse(V("w")), Coarse(V("v")));
        Formula premise = And(Reach(V("e"), V("f")), same);
        Formula conclusion = Reach(State(V("e"), V("w")), State(V("f"), V("v")));
        return Disp(All("M,e,f,w,v", Imp(premise, conclusion)));
    }
    private static Formula CharacterizationFormula()
    {
        Formula initial = Call("e0", V("M"));
        Formula left = EqOf(State(initial, V("w")), V("e"));
        Formula right = EqOf(State(initial, V("v")), V("f"));
        Formula same = EqOf(Coarse(V("w")), Coarse(V("v")));
        Formula witness = And(left, And(right, same));
        Formula represented = Some("w,v", witness);
        Formula equivalence = Seq(Par(Reach(V("e"), V("f"))), Sp, Iff, Sp, Par(represented));
        return Disp(All("M,e,f", equivalence));
    }
    private static Formula FactorizationFormula()
    {
        Formula invariant = Call("pairActionInvariant", V("M"));
        Formula through = Call("FactorsThrough", Call("historyAction", V("M")), Seq(V("kappa"), Underscore, Grp(V("hist"))));
        Formula equivalence = Seq(Par(invariant), Sp, Iff, Sp, Par(through));
        return Disp(All("M", equivalence));
    }
}
