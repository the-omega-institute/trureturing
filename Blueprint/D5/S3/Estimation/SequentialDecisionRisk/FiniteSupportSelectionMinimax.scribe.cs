using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class FiniteSupportSelectionMinimaxDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionMinimax.result";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Support Selection Bayes and Minimax Bridge.",
        H("Finite Support Selection Bayes and Minimax Bridge"),
        Blocks(Describe.Lean(
            DescribeId.Create("finitesupportselectionminimax"),
            DeclarationHandle.Create(Declaration),
            H("Finite Support Selection Bayes and Minimax Bridge"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every natural M, q and s, assume 1<=q<M, 0<r<1 and 0<=a<1, where a=rq/(M-q). The conclusion holds for both complete finite experiments: independent uniform-start ordered pairs and a consecutive path with one uniform start. The support is a single unknown q-element subset throughout all observations.")),
                Paragraph(Text("The conclusion includes stochastic compensated transitions and complete observation laws, strict positivity, the full uniform-reference and support-product likelihood factorizations, positive exponential weights, the normalized posterior, the exact elementary-symmetric inclusion-difference identity, and equivalence of inclusion and weight ordering.")),
                Paragraph(Text("Every permutation of the first-copy coordinates fixes the second copy and acts on every vertex in the complete observation. Mapping every support coordinate gives a bijection on supports; mapping both endpoints of every ordered pair, or every vertex of a path, gives a bijection on complete observations. Applying these explicit maps preserves the actual probability, relabels every weight, and transports the uniform cutoff decision mass. Any two supports of cardinality q are connected by one such permutation.")),
                Paragraph(Text("There exist measurable stochastic decision kernels equal to the uniform top-q rule and its extension by zero to other subsets. The q-element kernel has the exact cutoff description: H={i:t<w(i)}, E={i:w(i)=t}, |H|<q<=|H|+|E|, with uniform mass 1/binomial(|E|,q-|H|) on precisely those T between H and H union E.")),
                Paragraph(Text("For normalized Hamming loss, competitors output exactly q elements. For exact-recovery loss, competitors may output any subset. In each action class the constructed kernel minimizes uniform-prior Bayes cost among all randomized competitors, has equal frequentist risk at all true supports, and its risk at every support is at most the supremum risk of every competitor. Its supremum risk equals the infimum, over all randomized competitors, of their supremum risks."))),
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
        Call("Conclusion", F.Id("M"), F.Id("q"), F.Id("s"), F.Id("r"), F.Id("e"))));
}
