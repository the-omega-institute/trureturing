using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class ShortReturnWidthTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/ReturnWords/ShortReturnWidthTransport.";
    private static readonly Formula A = F.Id("a"), B = F.Id("b"), N = F.Id("n"), P = F.Id("p");
    private static readonly Formula G = F.Id("g"), D = F.Id("d"), W = F.Id("w");
    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula TwiceMinusOne => Sub(Mul(Digit(2), N), Digit(1));
    private static Formula Bound => Mul(Mul(P, FloorDiv(N, P)), FloorDiv(TwiceMinusOne, P));
    private static Formula Sync => Call("lcm", A, B);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short return lengths, phase divisibility, and contraction width estimates.",
        H("Short return width transport"),
        Blocks(
            Paragraph(Text(
                "These are abstract arithmetic estimates for the final step of a short-return "
                + "argument. All lengths and periods are natural numbers; division of natural "
                + "numbers means floor division, and natural subtraction is truncated at zero. "
                + "The contraction, root width d and piece width w are real numbers.")),
            Describe.Lean(
                DescribeId.Create("short-return-synchronization-bound"),
                DeclarationHandle.Create(Prefix + "synchronized_length_le_phase_bound"),
                H("Phase divisibility bounds the synchronization length"),
                StatementSource.FromAuthor(Disp(AllNat(new[] { "a", "b", "n", "p" },
                    Imp(LengthHypotheses(), Le(Sync, Bound))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Writing a=p alpha and b=p gamma gives lcm(a,b)=p lcm(alpha,gamma). "
                    + "The two quotient bounds and lcm(alpha,gamma)<=alpha gamma give the "
                    + "stated estimate. Zero lengths are allowed in this arithmetic lemma."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("short-return-contraction-antitone"),
                DeclarationHandle.Create(Prefix + "contraction_ratio_antitone"),
                H("The contraction ratio decreases with the positive scale"),
                StatementSource.FromAuthor(Disp(AllReal(new[] { "g" },
                    AllNat(new[] { "L", "M" }, Imp(
                        Conj(Lt(Digit(0), G), Lt(G, Digit(1)), Lt(Digit(0), F.Id("L")),
                            Le(F.Id("L"), F.Id("M"))),
                        Le(Ratio(F.Id("M")), Ratio(F.Id("L")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The larger exponent decreases the numerator and increases the denominator. "
                    + "Both denominators are positive. Equality of the two scales is included."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("short-return-width-lower-bound"),
                DeclarationHandle.Create(Prefix + "short_return_width_lower_bound"),
                H("Transport a synchronized packing estimate to the uniform scale"),
                StatementSource.FromAuthor(Disp(AllNat(new[] { "a", "b", "n", "p" },
                    AllReal(new[] { "g", "d", "w" }, Imp(
                        Conj(Lt(Digit(0), G), Lt(G, Digit(1)), Le(Digit(0), D),
                            LengthHypotheses(), Lt(Digit(0), A), Lt(Digit(0), B),
                            Le(Mul(Pow(G, Sync), D), Mul(Sub(Digit(1), Pow(G, Sync)), W))),
                        Le(Mul(Ratio(Bound), D), W)))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Put M=p floor(n/p) floor((2n-1)/p). For a pair of positive return lengths, "
                        + "the supplied packing inequality "
                        + "at L=lcm(a,b) first yields w>=g^L d/(1-g^L). The phase bound "
                        + "gives L<=M, and the preceding monotonicity lemma transports this to "
                        + "w>=g^M d/(1-g^M). Nonnegative d suffices; for an actual guard-root "
                        + "width d is positive. The packing premise itself forces w to be "
                        + "nonnegative, so a separate sign hypothesis on w is unnecessary.")),
                    Paragraph(Text(
                        "To obtain Proposition 51.3 for every original piece, one still needs "
                        + "actual returns at each basepoint with a<=n and b<=2n-1 whose first "
                        + "words differ after LCM synchronization, period divisibility from the "
                        + "second projection, and the original full-cylinder packing inequality. "
                        + "The coherence and phase characterization in CoherentReturnPathTemplates "
                        + "does not by itself supply these short returns or the packing inequality. "
                        + "The SevenCycleCoherence modules concern a particular original paired "
                        + "graph and do not supply the general bridge. These estimates assert "
                        + "neither the required SCC/source bridge nor existence of a graph realization."))),
                DescribeRole.Theorem))));

    private static Formula LengthHypotheses() => Conj(Lt(Digit(0), P),
        Divides(P, A), Divides(P, B), Le(A, N), Le(B, TwiceMinusOne));
    private static Formula Ratio(Formula exponent) =>
        new Formula.Fraction(Pow(G, exponent), Sub(Digit(1), Pow(G, exponent)));
    private static Formula FloorDiv(Formula x, Formula y) =>
        Seq(Lfloor, new Formula.Fraction(x, y), Rfloor);
    private static Formula Digit(byte digit) => F.D(digit);
    private static Formula AllNat(string[] names, Formula body) => All(names, NatType, body);
    private static Formula AllReal(string[] names, Formula body) => All(names, RealType, body);
    private static Formula All(string[] names, Formula type, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(names[i]), type, body);
        return body;
    }
    private static Formula Conj(params Formula[] parts)
    {
        var body = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            body = new Formula.Logic(parts[i], FormulaLogicOperator.And, body);
        return body;
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Divides(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Divides, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
}
