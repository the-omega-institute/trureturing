using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class EscapeRegimeCorollaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed finite output systems admit only the full-escape large-address regime.",
        H("Realizable Escape Regimes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("escape-probability-realizable-regimes"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbability/EscapeRegimeCorollary."
                        + "escape_probability_realizable_regimes"),
                H("The fixed-output escape regimes reduce to full escape"),
                StatementSource.FromAuthor(RegimeCorollaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite nonempty output alphabet, let f map Y to itself, "
                            + "write n for the size of Y and k for the number of fixed points. "
                            + "If k is zero, every address count has escape probability one. On "
                            + "positive address counts the probability is nondecreasing, and at "
                            + "one address it is one minus k divided by n. When n is at least two, "
                            + "the probability is strictly increasing if k is positive and tends "
                            + "to one as the address count grows.")),
                    Paragraph(Text(
                        "The same theorem records the unconditional model constraint k at most n. "
                            + "When n is at least two, the scaled weight k A n to the minus A lies "
                            + "between zero and the two stated geometric envelopes, tends to zero, "
                            + "and therefore cannot tend to a positive lambda. Under that same "
                            + "size condition, every density c strictly between zero and one has "
                            + "a finite threshold beyond which k cannot equal c n to the A.")),
                    Paragraph(Text(
                        "The proof applies the repository's exact closed-form, monotonicity, "
                            + "strict-monotonicity, fixed-output limit, geometric-decay, and "
                            + "positive-density exclusion theorems. Pinned Mathlib and Loogle "
                            + "contain no theorem combining these clauses; Mathlib's "
                            + "Fintype.card_subtype_le supplies the structural count bound. The "
                            + "conjunction preserves every mathematical clause of the named "
                            + "corollary, including its positive-address guard."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Asymptotics/DensePhaseUnrealizable")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Asymptotics/EscapeProbability/FixedOutputLimit")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Asymptotics/EscapeProbability/StrictAddressMonotonicity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Asymptotics/EscapeProbabilityMonotone")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Asymptotics/PoissonWeightDecay")),
        ]));

    private static Formula RegimeCorollaryFormula()
    {
        Formula y = F.Id("Y");
        Formula f = F.Id("f");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula a = F.Id("A");
        Formula a0 = new Formula.Subscript(a, D(0));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula Escape(Formula address) =>
            Call("escapeProbability", Call("Fin", address), f);
        Formula Weight(Formula address) => Seq(
            k, Sp, address, Sp, n, Caret, Grp(Minus, address));
        Formula Limit(Formula body, Formula value) => Seq(
            Lim, Underscore, Grp(a, To, Infty), Sp, body, Sp, Eq, Sp, value);

        var zeroFixedPoints = Seq(Left, Open,
            k, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            Forall, Sp, a, InMacro, naturals, Comma, Sp,
            Escape(a), Sp, Eq, Sp, D(1), Right, Close);
        var monotone = Call("MonotoneOn",
            Seq(Open, a, Sp, Mapsto, Sp, Escape(a), Close), Call("Ici", D(1)));
        var strict = Seq(Left, Open, Left, Open,
            n, Sp, Ge, Sp, D(2), Sp, Land, Sp,
            k, Sp, Gt, Sp, D(0), Right, Close, Sp, Rightarrow, Sp,
            Call("StrictMonoOn",
                Seq(Open, a, Sp, Mapsto, Sp, Escape(a), Close), Call("Ici", D(1))),
            Right, Close);
        var oneAddress = Seq(
            Escape(D(1)), Sp, Eq, Sp, D(1), Sp, Minus, Sp,
            Frac, Grp(k), Grp(n));
        var bounds = Seq(
            Forall, Sp, a, InMacro, naturals, Comma, Sp,
            D(0), Sp, Le, Sp, Weight(a), Sp, Le, Sp,
            a, Sp, n, Caret, Grp(D(1), Minus, a), Sp, Le, Sp,
            a, Sp, D(2), Caret, Grp(D(1), Minus, a));
        var positiveLimitExcluded = Seq(
            Forall, Sp, LambdaLower, InMacro, reals, Comma, Sp,
            LambdaLower, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
            Neg, Left, Open, Limit(Weight(a), LambdaLower), Right, Close);
        var denseScalingExcluded = Seq(
            Forall, Sp, F.Id("c"), InMacro, reals, Comma, Sp,
            D(0), Sp, Lt, Sp, F.Id("c"), Sp, Lt, Sp, D(1), Sp,
            Rightarrow, Sp, Exists, Sp, a0, InMacro, naturals, Comma, Sp,
            Forall, Sp, a, InMacro, naturals, Comma, Sp,
            a0, Sp, Le, Sp, a, Sp, Rightarrow, Sp,
            k, Sp, Neq, Sp, F.Id("c"), Sp, n, Caret, Grp(a));

        return Disp(Seq(
            Forall, Sp, y, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, y,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, y,
            CloseBracket, Comma, Sp,
            Forall, Sp, f, Colon, Sp, y, Sp, To, Sp, y, Comma, Esc,
            n, Sp, Eq, Sp, Call("card", y), Comma, Sp,
            k, Sp, Eq, Sp, Call("card", Call("Fix", f)), Comma, Sp,
            Left, Open, new Formula.Aligned([
                zeroFixedPoints,
                Seq(Land, Sp, monotone),
                Seq(Land, Sp, strict),
                Seq(Land, Sp, oneAddress),
                Seq(Land, Sp, Left, Open,
                    n, Sp, Ge, Sp, D(2), Sp, Rightarrow, Sp,
                    Limit(Escape(a), D(1)), Right, Close),
                Seq(Land, Sp, k, Sp, Le, Sp, n),
                Seq(Land, Sp, Left, Open,
                    n, Sp, Ge, Sp, D(2), Sp, Rightarrow, Sp,
                    Left, Open, new Formula.Aligned([
                        bounds,
                        Seq(Land, Sp, Limit(Weight(a), D(0))),
                        Seq(Land, Sp, positiveLimitExcluded),
                    ]), Right, Close, Right, Close),
                Seq(Land, Sp, Left, Open,
                    n, Sp, Ge, Sp, D(2), Sp, Rightarrow, Sp,
                    Left, Open, denseScalingExcluded, Right, Close,
                    Right, Close),
            ]), Right, Close, Dot));
    }
}
