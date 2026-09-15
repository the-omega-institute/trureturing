using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class NormOneCriticalPrimeTowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/NormOneCriticalPrimeTowers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One golden-trace recurrence has two complete prime-power fixed-point towers. "
            + "The result refutes the strongest natural reading of the critical-prime "
            + "uniqueness observation following Benfield-Lippard Conjecture 6.5.",
        H("Two Critical Prime Towers in One Golden Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("norm-one-exact-tower-engine"),
                DeclarationHandle.Create(Prefix + "order_tower_of_seed"),
                H("A primitive first defect controls every exponent"),
                StatementSource.FromAuthor(SeedTower()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p be an odd prime, A and B integer two-by-two "
                        + "matrices, A^p=I+p*B, and the actual order of A modulo p be p. "
                        + "Assume one specified entry of B is not divisible by p. "
                        + "For every e>0, the order modulo p^e is then exactly p^e.")),
                    Paragraph(Text("The imported binomial theorem is applied in the "
                        + "commutative polynomial ring Z[X] and then evaluated at B. "
                        + "It is not directly applied to a supposedly commutative "
                        + "matrix ring. The resulting coefficient remains B+p*C. "
                        + "Its primitive entry excludes the preceding p-power exponent, "
                        + "so the proof establishes minimality as well as a return."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-trace-three-power-tower"),
                DeclarationHandle.Create(Prefix + "golden_trace_three_tower"),
                H("Every positive power of three is fixed"),
                StatementSource.FromAuthor(Tower(D(3))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same integral companion A=[[47,-1],[1,0]] "
                    + "has A^3=I+3*[[34576,-736],[736,-16]]. The top-left defect "
                    + "is nonzero modulo three. The finite seed is consumed by this "
                    + "unbounded theorem, not published as a stand-alone positive instance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-trace-five-power-tower"),
                DeclarationHandle.Create(Prefix + "golden_trace_five_tower"),
                H("Every positive power of five is fixed for the same parameter"),
                StatementSource.FromAuthor(Tower(D(5))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the identical A, A^5=I+5*" 
                    + "[[45785971,-974611],[974611,-20746]], again with primitive "
                    + "top-left entry. Both towers use the original LucasCompanion "
                    + "period definition, with sequence semantics imported from "
                    + "NormOneCriticalPrimes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-prime-uniqueness-refuted"),
                DeclarationHandle.Create(Prefix + "refutes_critical_prime_uniqueness"),
                H("Uniqueness fails even with an all-exponent requirement"),
                StatementSource.FromAuthor(Call("Not", F.Id("criticalPrimeUniqueness"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("FullCriticalTower(a,p) requires primality and "
                    + "period(a,p^e)=p^e for every e>0. At a=47 both p=3 and p=5 "
                    + "satisfy it. This corrects the unnumbered critical-prime "
                    + "observation after Conjecture 6.5. It is reported together "
                    + "with the numbered conjecture refutation as one proof family. "
                    + "Neither 3 nor 5 is asserted to be a classical WSS prime."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(xs[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Tower(Formula p) => Disp(Call("Implies", Call("Positive", F.Id("e")),
        Call("Eq", Call("period", D(4, 7), Call("Power", p, F.Id("e"))),
            Call("Power", p, F.Id("e")))));

    private static Formula SeedTower() => Disp(Call("Eq",
        Call("order", Call("reduce", Call("Power", F.Id("p"), F.Id("e")), F.Id("A"))),
        Call("Power", F.Id("p"), F.Id("e"))));
}
