using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TwistedResetPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/TwistedResetPaths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact path sums and support for complement-twisted reset loops.",
        H("Twisted Reset Paths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-twisted-power-support"),
                DeclarationHandle.Create(Prefix + "twisted_power_support"),
                H("Twisted power support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k, real p, natural L, and state s = (b,j) in State k = Bool times Fin k, "
                    + "if the L-step matrix entry of K = kernel k p from s to flip(s) = (!b,j) is nonzero, then "
                    + "j.val < L. Thus every nonzero complement-twisted return starts below its return length; "
                    + "no positivity or stochasticity assumption on p is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-twisted-prefix-marginal"),
                DeclarationHandle.Create(Prefix + "twisted_prefix_marginal"),
                H("Exact complete-prefix marginal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k,n,G, real p, state s in State k, and map v : Fin n -> State k, let x be "
                    + "the endpoint after the n transitions specified by v. Summing over all maps w : Fin G -> "
                    + "State k, retaining the product pathWeight k p n s v times pathWeight k p G x w exactly "
                    + "when the closing endpoint is flip(s) and otherwise contributing zero, equals that prefix "
                    + "product times the (x, flip(s)) entry of (kernel k p)^G. No initial stationary factor appears."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-twisted-prefix-support"),
                DeclarationHandle.Create(Prefix + "twisted_prefix_support"),
                H("Support of every complete prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k,n,G, real p with 0 <= p, state s in State k, and map v : Fin n -> State k, "
                    + "if n + G <= s.2.val then twistedPrefixMass k p n G s v is zero. Here the mass sums the "
                    + "nonnegative n-step prefix weight with every G-step closing continuation that reaches flip(s); "
                    + "the cutoff excludes all such complete twisted paths of nonzero weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-twisted-prefix-total-mass"),
                DeclarationHandle.Create(Prefix + "twisted_prefix_total_mass"),
                H("Total prefix mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k,n,G and real p, summing twistedPrefixMass k p n G s v over every start "
                    + "state s in State k and every map v : Fin n -> State k equals loopMass k p (n + G). The "
                    + "latter is the sum, over all s, of the (s, flip(s)) entries of (kernel k p)^(n+G), so the "
                    + "complete-prefix and twisted-loop masses have exactly the same total."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-loop-mass-pos"),
                DeclarationHandle.Create(Prefix + "loop_mass_pos"),
                H("Positive loop mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k with k >= 2, every real p with p > 0, and every natural L with L >= 2, "
                    + "the twisted loop mass loopMass k p L is strictly positive. Odd L have reset-only positive "
                    + "loops, while even L have a positive loop with one increment followed by an odd number of "
                    + "resets; no lower bound on a stationary mass is assumed."))),
                DescribeRole.Theorem))));
}
