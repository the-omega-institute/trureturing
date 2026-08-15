using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class ConditionalEntropyStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Full support identifies stability depth with first zero conditional entropy.",
            H("Prediction Stability from Zero Conditional Entropy"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("prediction-stability-depth-is-first-zero-conditional-entropy"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability."
                            + "prediction_stability_depth_eq_conditional_entropy_zero"),
                    H("Prediction stability depth is the first zero conditional entropy"),
                    StatementSource.FromAuthor(StabilityFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let Y and O be finite types, tau a deterministic state update, "
                                + "q a readout, and p a strictly positive real weight on every "
                                + "state. The word at depth m consists of the readouts at times "
                                + "zero through m. Prediction is stable at m when equality of "
                                + "those words forces equality of the readout at time m+1.")),
                        Paragraph(Text(
                            "The joint weight nextReadoutJointLaw records each depth-m word "
                                + "together with its next readout. Strict positivity makes every "
                                + "realized word fiber carry positive mass. The frozen repository "
                                + "theorem conditional_entropy_eq_zero_iff_point_mass_on_support "
                                + "then says exactly that each such fiber has one next-readout "
                                + "value. Equality of the stable-depth set and zero-entropy-depth "
                                + "set yields equality of their natural infima.")),
                        Paragraph(Text(
                            "The pinned-library search found Nat.sInf_mem and Nat.sInf_def for "
                                + "the minimum semantics and Finset.single_le_sum for positivity "
                                + "of a realized pushforward cell; all three are applied in Lean. "
                                + "The library has no matching finite conditional-entropy theorem. "
                                + "LeanSearch returned only unrelated binary-entropy and "
                                + "measure-level conditional-distribution results, while the "
                                + "repository search found the slice-level theorem but no "
                                + "prediction-depth characterization.")),
                        Paragraph(Text(
                            "A normalized full-support probability law is a special case: "
                                + "normalization is not required because the conditional ratios "
                                + "and their point-mass property are unchanged by positive common "
                                + "scaling. The theorem is finite and deterministic. It supplies "
                                + "no stochastic-process or measure-theoretic extension and no "
                                + "quantitative upper bound on the first stable depth."))),
                    DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula NamedCall(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname,
            Grp(F.Id(name)),
            Open,
        };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula StabilityFormula()
    {
        Formula yType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula tau = F.Id("tau");
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        Formula m = F.Id("m");
        Formula y = F.Id("y");
        Formula nextLaw = NamedCall("nextReadoutJointLaw", tau, q, p, m);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, yType, Comma, Sp, outputType, Comma, Sp,
            Typeclass("Fintype", yType), Sp,
            Typeclass("Fintype", outputType), Comma, RowBreak,
            tau, Colon, Sp, yType, Sp, To, Sp, yType, Comma, Sp,
            q, Colon, Sp, yType, Sp, To, Sp, outputType, Comma, Sp,
            p, Colon, Sp, yType, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
            Open, Forall, Sp, y, Comma, Sp,
            D(0), Sp, Lt, Sp, p, Open, y, Close, Close,
            Sp, Rightarrow, RowBreak,
            NamedCall("predictionStabilityDepth", tau, q), Sp, Eq, Sp,
            Operatorname, Grp(F.Id("sInf")), Sp,
            OpenBrace, m, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp,
            Mid, Sp, NamedCall("conditionalEntropy", nextLaw), Sp, Eq, Sp, D(0),
            CloseBrace, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
