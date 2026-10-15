using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class UnifilarPairSurvivalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The affinity of words whose two unifilar trajectories have not merged equals a killed pair matrix row sum at every length.",
        H("Unifilar word affinity and pair survival"),
        Blocks(
            Describe.Lean(DescribeId.Create("sum-words"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.sum_words"),
                H("sum words"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every real sum over Boolean words of length n+1 equals the sum over the first Boolean symbol and all length-n tails. UnifilarAffinityContraction.word_total and the existing pair recurrence consume the same equivalence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pair-matrix-action"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.pairMatrix_action"),
                H("pairMatrix action"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any real test function on distinct pairs, the pairMatrix row action is exactly the sum over common symbols of their square-root weight times the successor-pair test value, discarding merged successors. The strict contraction proof uses this identity with the constant-one test function."))), DescribeRole.Theorem),
            Paragraph(Text("Let H be a finite state set. A single successor function delta maps a state and an emitted Boolean symbol to its next state. The nonnegative symbol mass p(a,x) belongs to this same producer. For a word w of length n, endpoint(delta,n,a,w) follows its deterministic trajectory and wordMass(p,delta,n,a,w) multiplies its successive symbol masses. Empty words retain their starting state and have mass one. Zero symbol masses are allowed; their chosen successors have zero contribution.")),
            Paragraph(Text("Pair H consists of ordered distinct state pairs. The matrix pairMatrix(p,delta) uses one common symbol on both trajectories, assigns weight sqrt(p(a,x)p(b,x)), and discards a transition if its successor states coincide. Its entries sum the weights of all symbols with the specified ordered successor pair. survivingAffinity(p,delta,n,s) uses the existing Bhattacharyya coefficient on the two word-mass functions, masking the first function to zero precisely on words with coincident endpoints. Thus it is the sum of sqrt(P(a,w)P(b,w)) over the nonmerged words, with both trajectories reading the same w.")),
            Describe.Lean(DescribeId.Create("pair-word-survival"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.pair_survival_word_affinity"),
                H("Exact nonmerged-word identity at every length"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Induct on the original emitted-bit length. Split every nonempty word into its first symbol and tail. If the first successors coincide, all later states coincide because the two trajectories use the same successor function and the same tail. Such words contribute zero. Otherwise the one-symbol square-root weight multiplies the surviving affinity from the resulting distinct pair. Expanding the matrix product gives precisely this recurrence. At length zero the identity matrix has row sum one and the unique empty word has affinity one.")),
                    Paragraph(Text("Square-root weights on common-symbol pair paths are used in the quantum pairwise-merger construction of Riechers, Mahoney, Aghamohammadi and Crutchfield, A Closed-Form Shave from Occam's Quantum Razor: Exact Results for Quantum Compression, Section IV (https://arxiv.org/html/1510.08186v1). Their construction adds a synchronization sink and removes pairs without a path to it. The survival matrix here retains all ordered distinct pairs and discards transitions that merge their states.")),
                    Paragraph(Text("For the row-unifilar marked quotient of FIB legal-edge producers, p and delta are its actual symbol masses and successors. The identity is the pair-process step behind geometric classification estimates: it retains words with distinct final quotient states rather than multiplying independent visible marginals. No row normalization or stationarity is needed for this algebraic identity. It therefore also applies to subprobability weights. Stochasticity, a distinguishing block, MAP error comparisons and conditional erasure estimates require separate hypotheses. No all-producer summability, uniform rate, posterior band, attainment or finite-hidden separation is established here."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Statement()
    {
        Formula h = F.Id("H"), p = F.Id("p"), delta = F.Id("d"), n = F.Id("n"), s = F.Id("s"), t = F.Id("t");
        Formula real = Seq(Mathbb, Grp(F.Id("R"))), nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula b = Call("Bool"), pairs = Call("Pair", h);
        Formula nonnegative = All("a", h, All("x", b,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(p, [F.Id("a"), F.Id("x")]))));
        Formula matrix = new Formula.Power(Par(Call("pairMatrix", p, delta)), n);
        Formula rowSum = Seq(new Formula.Subscript(Sum, Seq(t, Colon, Sp, pairs)), Sp,
            new Formula.Apply(matrix, [s, t]));
        Formula equation = new Formula.Relation(rowSum, FormulaRelationOperator.Equal,
            Call("survivingAffinity", p, delta, n, s));
        return Disp(All("H", Call("Type"), Seq(OpenBracket, Call("Fintype", h), CloseBracket, Sp,
            All("p", Arrow(h, Arrow(b, real)), All("d", Arrow(h, Arrow(b, h)),
                new Formula.Logic(Par(nonnegative), FormulaLogicOperator.Implies,
                    Par(All("n", nat, All("s", pairs, equation)))))))));
    }
}
