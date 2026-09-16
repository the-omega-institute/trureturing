using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class DriftMixtureMomentIdentifiabilityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Monodromy/DriftMixtureMomentIdentifiability.uniform_mixture_decoder_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single decoder of four pooled second moments exists for all finite "
            + "balanced calibration mixtures exactly below a sharp drift bound. "
            + "Beyond it, explicit admissible ensembles have identical full records.",
        H("Sharp Moment Identifiability under Balanced Drift"),
        Blocks(
            Paragraph(Text(
                "Reuse the actual records of GainRobustGaussianDiscrimination. "
                    + "For arbitrary finite n, sum records(c,g_r,o_r,s_r,t_r) "
                    + "over r in Fin(n). The effective gains g_r are nonnegative "
                    + "and their sum is positive. Each s_r and t_r belongs to "
                    + "[1-delta,1+delta]. The offsets o_r are arbitrary. "
                    + "Exposure weights are absorbed into g_r and o_r. "
                    + "All four setting classes use this same ensemble, even "
                    + "though calibration can change arbitrarily across r.")),
            Describe.Lean(
                DescribeId.Create("uniform-mixture-decoder-iff"),
                DeclarationHandle.Create(Declaration),
                H("Exact existence criterion for every possible four-record decoder"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume 0<cLo<cHi and 0<=delta<1. The left-hand property "
                            + "is the existence of one function from four real "
                            + "records to Bool, returning false for cLo and true "
                            + "for cHi, for every n and every admissible calibration "
                            + "ensemble. The criterion is "
                            + "(cLo+cHi)delta squared<cHi-cLo. This quantifies "
                            + "over all deterministic nonlinear decoders; it is "
                            + "not restricted to a supplied threshold architecture.")),
                    Paragraph(Text(
                        "The proof computes a=r1-r0=A=sum(g s squared), "
                            + "b=r2-r0=2B with B=sum(g t squared), and "
                            + "d=r3-r1-r2+r0=2cC with C=sum(g s t). "
                            + "Thus R=d squared/(2ab)=c squared C squared/(AB). "
                            + "Positive mass and positive pulse gains prove all "
                            + "denominators nonzero. Weighted Cauchy-Schwarz "
                            + "gives C squared<=AB. A sharp reverse estimate "
                            + "gives C squared/(AB)>=((1-delta squared)/" 
                            + "(1+delta squared)) squared.")),
                    Paragraph(Text(
                        "For sufficiency put kappa=((1-delta squared)/" 
                            + "(1+delta squared)) squared. The same threshold "
                            + "tau=(cLo squared+kappa cHi squared)/2 separates "
                            + "every admissible normalized contrast. For necessity "
                            + "let x=(cHi-cLo)/(cHi+cLo), d=sqrt(x), and "
                            + "a=sqrt(1+x). Mix the high-correlation gains "
                            + "(1-d,1+d) and (1+d,1-d) with effective gains "
                            + "one half and zero offsets. Compare with the "
                            + "low-correlation constant gains (a,a), effective "
                            + "gain one and zero offset. Failure of the criterion "
                            + "puts every gain in the box. The proof computes "
                            + "equality of the complete four-real records, not "
                            + "merely equality of normalized contrast.")),
                    Paragraph(Text(
                        "The reverse inequality is classical Polya-Szego/Cassels "
                            + "prior art; see Dragomir, arXiv:math/0311212, for "
                            + "weighted reverse Cauchy-Schwarz context. It is "
                            + "an internal ingredient, not a separately claimed "
                            + "new theorem. The source's actual target is the "
                            + "all-decoder observer-fiber dichotomy for the "
                            + "specified control-record family.")),
                    Paragraph(Text(
                        "Balanced randomized assignment independent of exogenous "
                            + "calibration motivates a common ensemble at the "
                            + "expectation level. No finite random schedule is "
                            + "asserted to realize exactly identical weighted "
                            + "ensembles. Setting-dependent responses or unequal "
                            + "sampling weights need a separate error model. "
                            + "No Gaussian-measure existence, sampling theorem, "
                            + "or arbitrary-state entanglement certificate is "
                            + "exported by this module.")),
                    Paragraph(Text(
                        "A collision of four second moments is not a collision "
                            + "of the full Gaussian-mixture distributions. The "
                            + "companion theory gives a fourth-moment separation "
                            + "for the boundary example and a non-identically "
                            + "distributed randomized acquisition bound. Those "
                            + "are separate ordinary mathematical deductions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Statement() => Disp(Seq(
        Call("OrderedPositiveCandidates", F.Id("cLo"), F.Id("cHi")), Sp, Land, Sp,
        Call("DriftHalfWidthInUnitInterval", F.Id("delta")), Sp, Rightarrow, Sp,
        new Formula.Relation(
            Call("ExistsOneDecoderForAllFiniteBalancedMixtures", F.Id("cLo"),
                F.Id("cHi"), F.Id("delta")),
            FormulaRelationOperator.Equal,
            Call("SharpDriftInequality", F.Id("cLo"), F.Id("cHi"), F.Id("delta")))));
}
