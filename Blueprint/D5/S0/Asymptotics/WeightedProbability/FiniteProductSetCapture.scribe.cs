using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class FiniteProductSetCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = F.Id("a");
        var ap = Seq(a, Apos);
        var b = F.Id("b");
        var f = F.Id("f");
        var q = F.Id("q");
        var t = F.Id("T");
        var address = F.Id("A");
        var cardT = Seq(Lvert, Sp, t, Sp, Rvert);
        var fixedPower = Call("fixedPowerMass", q, f, b, cardT);
        var collisionPower = Call("collisionPowerMass", q, f, b, cardT);
        var setMass = Call("setCaptureProbability", q, f, t);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every prescribed finite set of captured addresses has an exact all-orders weighted intersection mass.",
            H("Finite Product Set Capture Law"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("all-orders-weighted-capture-intersection"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture."
                        + "set_capture_probability_exact"),
                    H("Exact prescribed-set capture probability"),
                    StatementSource.FromAuthor(Disp(Seq(
                        setMass, Sp, Eq, Sp,
                        Prod, Underscore, Grp(b, InMacro, Sp, t), Sp, fixedPower, Sp,
                        Prod, Underscore,
                        Grp(b, InMacro, Sp, Grp(address, Setminus, Sp, t)), Sp,
                        collisionPower, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Conditioning on the listing diagonal lets constrainedRows_weight_sum integrate out every free row and retain precisely the rows indexed by T.")),
                        Paragraph(Text(
                            "Finite sum-product factorization then separates columns: selected columns contribute fixedPowerMass and unselected columns contribute collisionPowerMass, both at exponent |T|."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("singleton-set-law-agrees-with-frozen-capture-law"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture."
                        + "singleton_set_formula_eq_capture_probability_exact"),
                    H("Singleton consistency"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("setFormula", q, f, OpenBrace, a, CloseBrace), Sp, Eq, Sp,
                        Call("oneRowFormula", q, f, a), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The proof applies the all-orders theorem and the frozen capture_probability_exact theorem to the same singleton event."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("pair-set-law-agrees-with-frozen-pair-law"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture."
                        + "pair_set_formula_eq_pair_capture_probability_exact"),
                    H("Distinct-pair consistency"),
                    StatementSource.FromAuthor(Disp(Seq(
                        a, Neq, Sp, ap, Sp, Rightarrow, Sp,
                        Call("setFormula", q, f, OpenBrace, a, Comma, Sp, ap, CloseBrace),
                        Sp, Eq, Sp, Call("pairFormula", q, f, a, ap), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For distinct addresses, the proof applies the all-orders theorem and the frozen pair_capture_probability_exact theorem to the same two-address event."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture")),
            ]));
    }
}
