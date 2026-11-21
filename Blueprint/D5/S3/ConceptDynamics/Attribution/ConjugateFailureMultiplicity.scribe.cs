using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ConjugateFailureMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity."
        + "normal_closure_loss_gap_and_eq";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting the occurrences of each seed in distinct conjugate failure events.",
        H("Fixed mass under normal closure"),
        Blocks(Describe.Lean(
            DescribeId.Create("normal-closure-loss-gap-and-eq"),
            DeclarationHandle.Create(Gid),
            H("Exact loss gap and equality criterion"),
            StatementSource.FromAuthor(Gap()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let G act on a finite set S with nonnegative invariant real weights a. "
                    + "Write T for the sum of all the weights and M(K) for the weight of the "
                    + "seeds fixed by a subgroup K. Let N be the normal closure of H in G.")),
                Paragraph(Text("For each g in G, the failure event consists of the seeds moved "
                    + "by an element of the conjugate of H by g. Count each different event once "
                    + "and write r for their number. For a seed s write C(s) for the number of "
                    + "events containing it. Write L(K) for T minus M(K).")),
                Paragraph(Text("For any natural number d, the expression on the left is the "
                    + "sum on the right, with SumMoved ranging over seeds moved by N. If d is a lower bound on "
                    + "C(s) for all positive-weight seeds moved by N, that expression is "
                    + "nonnegative. It equals zero exactly when every such seed has C(s) equal to d.")),
                Paragraph(Text("Weight invariance gives the same loss for every conjugate "
                    + "event. Counting by seed gives the weighted multiplicity, which is zero "
                    + "on a seed fixed by N. Subtracting d times the loss for N gives the "
                    + "formula. On the stated support every summand is nonnegative. Each "
                    + "positive-weight moved seed then contributes zero exactly at multiplicity d."))),
            DescribeRole.Theorem))));

    private static Formula Gap()
    {
        Formula seed = F.Id("s");
        Formula excess = Seq(Open, Apply("C", seed), Sp, Minus, Sp, F.Id("d"), Close);
        return Disp(Seq(F.Id("r"), Sp, Apply("L", F.Id("H")), Sp, Minus, Sp,
            F.Id("d"), Sp, Apply("L", F.Id("N")), Sp, Eq, Sp,
            Apply("SumMoved", seed, Seq(Apply("a", seed), Sp, excess))));
    }

    private static Formula Apply(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
