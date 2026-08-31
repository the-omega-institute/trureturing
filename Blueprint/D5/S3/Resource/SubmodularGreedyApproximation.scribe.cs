using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class SubmodularGreedyApproximationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Resource/SubmodularGreedyApproximation."
            + "cardinality_greedy_one_sub_inv_exp_guarantee";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cardinality-greedy maximization of a monotone submodular function "
            + "attains the classical one-minus-one-over-e guarantee.",
        H("The Submodular Greedy Approximation Guarantee"),
        Blocks(Describe.Lean(
            DescribeId.Create("cardinality-greedy-one-minus-one-over-e-guarantee"),
            DeclarationHandle.Create(Declaration),
            H("Cardinality greedy attains one minus one over e"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/nemhauserwolseyfisher1978submodular")),
            Blocks(
                Paragraph(Text(
                    "Let f be a real-valued function on finite subsets, normalized by "
                        + "f(empty) = 0, monotone under inclusion, and submodular in "
                        + "diminishing-returns form. At each of k steps, choose a fresh "
                        + "element whose marginal value is maximal among all unchosen "
                        + "elements.")),
                Paragraph(Text(
                    "For every comparison set O with at most k elements, submodularity "
                        + "bounds the remaining gap f(O) - f(S_t) by the sum of O's "
                        + "marginals at S_t. Greedy maximality bounds every summand by "
                        + "the next greedy gain, giving a geometric contraction by "
                        + "1 - 1/k.")),
                Paragraph(Text(
                    "After k steps, Mathlib's exponential power bound places the residual "
                        + "factor below exp(-1). The theorem does not require O to be "
                        + "globally optimal, so the displayed guarantee applies in "
                        + "particular to every optimal feasible set."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula comparison = F.Id("O");
        Formula greedy = new Formula.Subscript(F.Id("S"), F.Id("k"));
        Formula value(Formula set) => F.Seq(F.Id("f"), F.Open, set, F.Close);
        Formula factor = F.Seq(
            F.Left, F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            F.Frac, F.Grp(F.D(1)), F.Grp(F.Id("e")), F.Right, F.Close);
        return F.Disp(F.Seq(
            factor, F.Sp, value(comparison), F.Sp, F.Leq, F.Sp, value(greedy)));
    }
}
