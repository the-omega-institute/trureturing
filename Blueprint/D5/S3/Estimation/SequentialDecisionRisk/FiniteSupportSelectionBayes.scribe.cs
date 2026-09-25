using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class FiniteSupportSelectionBayesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes.finite_support_bayes";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Support Selection Bayes Rules.",
        H("Finite Support Selection Bayes Rules"),
        Blocks(Describe.Lean(
            DescribeId.Create("finitesupportselectionbayes"),
            DeclarationHandle.Create(Declaration),
            H("Finite Support Selection Bayes Rules"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The vertices are two copies of Fin M. A support S is a subset of the first copy with cardinality q, fixed for the whole observation. Write n = 2M and a = rq/(M-q). The source-row coefficient is r on S, -a on the other first-copy vertices, and zero on the second copy. The target sign is +1 on the first copy and -1 on the second. The transition probability is (1+b(S,x) chi(y))/n.")),
                Paragraph(Text("For every natural sample count s, the pair experiment consists of s independent ordered pairs, each with its own uniform start. The path experiment has exactly one uniform start and s consecutive transitions. Their complete observation probabilities are respectively the product of P(S,x,y)/n over pairs and the product of transitions divided by n. The compensated transition has all row and column sums equal to one, and both complete observation laws are strictly positive and stochastic.")),
                Paragraph(Text("For each first-copy coordinate i, let N(i,+) and N(i,-) count departures from i whose targets have sign +1 and -1. Set w(i)=((1+r)/(1-a))^N(i,+) ((1-r)/(1+a))^N(i,-), and W(i)=N(i,+) log((1+r)/(1-a))+N(i,-) log((1-r)/(1+a)). Then w(i)>0 and w(i)=exp(W(i)). The observation probability is its uniform reference mass times C times the product of w(i) over i in S. Here C is the product of 1-a chi(y) over edges starting in the first copy and is independent of S.")),
                Paragraph(Text("The uniform fixed-cardinality prior gives posterior mass proportional to the product of the selected weights. Its normalizer Z is the sum of these products over all q-element supports and is positive. For distinct i and j, the inclusion-probability difference is (w(i)-w(j)) times the sum of products over all (q-1)-element subsets excluding i and j, divided by Z. This coefficient is strictly positive, so inclusion probabilities and weights have exactly the same weak ordering.")),
                Paragraph(Text("The decision rule is uniform over q-element subsets whose selected weights dominate every omitted weight. There is a cutoff t with H={i:t<w(i)} and E={i:w(i)=t}, satisfying |H|<q<=|H|+|E|. Its mass at T is the reciprocal of binomial(|E|,q-|H|) when H is contained in T and T is contained in H union E, and zero otherwise. This is a stochastic kernel, including at sample count zero.")),
                Paragraph(Text("The rule minimizes uniform-prior expected normalized Hamming loss |T symmetric-difference S|/(2q) among all randomized rules with exactly q outputs. Extending it by zero to every other subset also gives a stochastic kernel and minimizes exact-recovery loss, zero for T=S and one otherwise, among all randomized rules with arbitrary-subset actions."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp, F.Id("q"), Comma, Sp, F.Id("s"), Colon, Sp,
        F.Id("Nat"), Comma, Sp, F.Id("r"), Colon, Sp, F.Id("Real"), Comma, Sp,
        F.Id("e"), Colon, Sp, F.Id("Experiment"), Comma, Sp,
        Num(1), Leq, F.Id("q"), Lt, F.Id("M"), Sp, Land, Sp,
        Num(0), Lt, F.Id("r"), Lt, Num(1), Sp, Land, Sp,
        Num(0), Leq, Call("compensation", F.Id("M"), F.Id("q"), F.Id("r")), Lt, Num(1),
        Sp, Rightarrow, Sp,
        Call("BayesCertificate", F.Id("M"), F.Id("q"), F.Id("s"), F.Id("r"), F.Id("e"))));
}
