using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class HellingerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/TotalVariation/Hellinger",
            "Intrinsic squared Hellinger distance is pinned on arbitrary finite real functions and compared sharply with total variation."),
        H("Squared Hellinger Distance and Total Variation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("squared-hellinger-distance-is-intrinsic-square-root-geometry"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.hellingerSq"),
                H("Squared Hellinger distance is intrinsic square-root geometry"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Colon, Eq,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    Open,
                    Sqrt, Sp, Grp(F.Id("p"), Open, F.Id("i"), Close), Minus,
                    Sqrt, Sp, Grp(F.Id("q"), Open, F.Id("i"), Close),
                    Close, Caret, Grp(D(2)), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite real functions p and q, the squared Hellinger distance is " +
                        "defined intrinsically as the sum of the squared coordinatewise gaps " +
                        "between their square roots. The definition itself requires neither " +
                        "nonnegativity nor normalization.")),
                    Paragraph(Text(
                        "Two forms were available: this square-root geometry and the probability-" +
                        "domain formula 2(1-BC(p,q)). The latter was deliberately rejected as a " +
                        "definition. It would make the bridge identity true by reflexivity, and " +
                        "an identity that holds by definition pins nothing. It would also build " +
                        "normalization-dependent coordinates into an object otherwise defined on " +
                        "arbitrary finite real functions.")),
                    Paragraph(Text(
                        "The choice records a general methodological principle: a definition must " +
                        "not be selected merely to make its own pinning identity trivial. The " +
                        "bridge to Bhattacharyya affinity is therefore proved between independently " +
                        "defined quantities."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("squared-hellinger-distance-vanishes-on-the-diagonal"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.hellinger_sq_self"),
                H("Squared Hellinger distance vanishes on the diagonal"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Comma, Sp, F.Id("p"), Close, Eq, D(0), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The definition is defended by four identities arranged in layers. Each " +
                        "successive layer governs a strictly larger domain of two-input behavior " +
                        "than the preceding pin can inspect. The first layer is the diagonal, and " +
                        "it establishes self-distance zero without hypotheses.")),
                    Paragraph(Text(
                        "This first identity cannot detect a corruption that ignores q entirely, " +
                        "such as summing (sqrt(p(i))-sqrt(p(i)))^2. The corruption also vanishes " +
                        "on every diagonal input, so it passes the self-distance theorem. The next " +
                        "layer must therefore leave the diagonal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probability-hellinger-square-is-twice-one-minus-affinity"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_two_sub"),
                H("Probability Hellinger square is twice one minus affinity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Eq,
                    D(2), Open, D(1), Minus,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The second layer governs pairs of probability vectors and proves the " +
                        "nontrivial bridge H^2(p,q)=2(1-BC(p,q)). It kills the one-sided " +
                        "corruption: on two opposite Bool point masses, the intrinsic value is " +
                        "two, whereas the corruption from the first layer remains zero.")),
                    Paragraph(Text(
                        "Normalization is essential to this coordinate form. Consequently, the " +
                        "identity still cannot inspect a corruption engineered to vanish whenever " +
                        "both total masses equal one. The third layer removes normalization while " +
                        "retaining the natural nonnegative mass-function domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonnegative-hellinger-square-expands-through-affinity"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_sum_add_sub_two_bhattacharyya"),
                H("Nonnegative Hellinger square expands through affinity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Eq,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Plus,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Minus,
                    D(2), Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The third layer governs nonnegative finite mass functions without " +
                        "normalization. A compiled corruption can augment the intrinsic expression " +
                        "by a diagonal-vanishing term proportional to " +
                        "(sum_i p(i)-1)^2(sum_i q(i)-1)^2. It passes self-distance because the " +
                        "added term vanishes on the diagonal, and it passes the probability bridge " +
                        "because both normalization defects vanish there.")),
                    Paragraph(Text(
                        "Off the normalized domain the corruption is exposed. On Unit with p=0 " +
                        "and q=4, it evaluates to 148 while the intrinsic squared Hellinger " +
                        "distance is four. The mass-expansion identity rules it out throughout the " +
                        "nonnegative, nonnormalized domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hellinger-square-has-an-all-real-algebraic-expansion"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_sum_expanded"),
                H("Hellinger square has an all-real algebraic expansion"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Eq,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    Open,
                    Sqrt, Sp, Grp(F.Id("p"), Open, F.Id("i"), Close),
                    Caret, Grp(D(2)), Plus,
                    Sqrt, Sp, Grp(F.Id("q"), Open, F.Id("i"), Close),
                    Caret, Grp(D(2)), Minus,
                    D(2), Open,
                    Sqrt, Sp, Grp(F.Id("p"), Open, F.Id("i"), Close),
                    Sqrt, Sp, Grp(F.Id("q"), Open, F.Id("i"), Close),
                    Close, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The fourth and final layer is a pure algebraic expansion valid for every " +
                        "finite real input. A corruption that activates only on negative " +
                        "coordinates can pass all three earlier layers. On Unit with p=-1 and " +
                        "q=0, the compiled corruption gives one, whereas the intrinsic value is " +
                        "zero because Real.sqrt of a negative number is zero. The all-real " +
                        "expansion detects it.")),
                    Paragraph(Text(
                        "This last identity closes the defense: no further corruption can survive " +
                        "because its right side is extensionally equal to the definition on every " +
                        "finite real input. Its proof is elementary ring algebra. It is cheap " +
                        "defensive infrastructure rather than deep mathematics, and its strength " +
                        "comes precisely from that complete extensional coverage.")),
                    Paragraph(Text(
                        "Every corruption and witness in the four-layer progression was compiled " +
                        "independently by the caller, including the negative-input fact used in " +
                        "the final case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-squared-square-root-gap-contracts-the-absolute-gap"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.sq_sqrt_sub_sqrt_le_abs_sub"),
                H("The squared square-root gap contracts the absolute gap"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Sqrt, Sp, Grp(F.Id("a")), Minus,
                    Sqrt, Sp, Grp(F.Id("b")), Close,
                    Caret, Grp(D(2)), Le, Sp,
                    Vert, Sp, F.Id("a"), Minus, F.Id("b"), Sp, Vert, Sp, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The scalar contraction is stated for arbitrary real a and b. No sign " +
                        "hypothesis is hidden in its signature. When both inputs are nonnegative, " +
                        "the usual factorization of a-b through their square roots gives the " +
                        "comparison.")),
                    Paragraph(Text(
                        "The remaining sign cases are not accidental exceptions. Real.sqrt is " +
                        "zero on nonpositive inputs, so the same inequality remains valid when one " +
                        "or both arguments are negative. This all-real scalar statement is exactly " +
                        "what permits the lower bracket to inherit no mass-function hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-hellinger-square-is-bounded-by-total-variation"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.hellinger_sq_div_two_le_total_variation"),
                H("Half the Hellinger square is bounded by total variation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Frac,
                    Grp(F.Id("H"), Caret, Grp(D(2)), Open,
                        F.Id("p"), Comma, Sp, F.Id("q"), Close),
                    Grp(D(2)),
                    Le, Sp,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The lower bracket H^2(p,q)/2 <= TV(p,q) holds for arbitrary finite real " +
                        "functions. In particular, p and q need not be nonnegative and need not " +
                        "be normalized. Summing the all-real scalar contraction coordinatewise " +
                        "and applying the factor one half in total variation proves the result.")),
                    Paragraph(Text(
                        "This strength follows from deriving the hypothesis set for the statement " +
                        "itself rather than copying assumptions from a neighboring theorem. That " +
                        "discipline has now produced strictly stronger results in six consecutive " +
                        "waves in this bucket."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-upper-bracket-is-the-frozen-affinity-bound-in-hellinger-coordinates"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.total_variation_sq_le_hellinger_sq_sub_quarter"),
                H("The upper bracket is the frozen affinity bound in Hellinger coordinates"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Caret, Grp(D(2)), Le, Sp,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Minus,
                    Frac,
                    Grp(Open,
                        F.Id("H"), Caret, Grp(D(2)), Open,
                        F.Id("p"), Comma, Sp, F.Id("q"), Close, Close,
                        Caret, Grp(D(2))),
                    Grp(D(4)), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This theorem is not new mathematics. It is the frozen bound " +
                        "TV(p,q)^2 <= 1-BC(p,q)^2 rewritten under the independently proved bridge " +
                        "H^2(p,q)=2(1-BC(p,q)). Thus the displayed term H^2-H^4/4 is only the " +
                        "Bhattacharyya square bound expressed in Hellinger coordinates.")),
                    Paragraph(Text(
                        "The restatement is included solely because it makes the two-sided " +
                        "comparison readable beside H^2(p,q)/2 <= TV(p,q). It must not be read as " +
                        "an independent inequality or a second analytic contribution. Unlike the " +
                        "lower bracket, this coordinate rewrite assumes that both inputs are " +
                        "nonnegative probability vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-lower-bracket-is-strict-on-a-bool-witness"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Hellinger.hellinger_sq_lower_strict_witness"),
                H("The lower bracket is strict on a Bool witness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    F.Id("p"), Eq,
                    Delta, Underscore, Grp(Operatorname, Grp(F.Id("true"))), Comma, RowBreak,
                    F.Id("q"), Open, Operatorname, Grp(F.Id("true")), Close, Eq,
                    Frac, Grp(D(9)), Grp(D(2, 5)), Comma, Sp,
                    F.Id("q"), Open, Operatorname, Grp(F.Id("false")), Close, Eq,
                    Frac, Grp(D(1, 6)), Grp(D(2, 5)), Comma, RowBreak,
                    Frac,
                    Grp(F.Id("H"), Caret, Grp(D(2)), Open,
                        F.Id("p"), Comma, Sp, F.Id("q"), Close),
                    Grp(D(2)), Lt,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The strictness statement is a theorem, not a comment. On Bool, p is the " +
                        "point mass at true and q assigns masses 9/25 and 16/25 to true and false, " +
                        "respectively. Lean evaluates the lower side as 2/5 and total variation as " +
                        "16/25, so the strict inequality is kernel-checked and frozen rather than " +
                        "asserted informally.")),
                    Paragraph(Text(
                        "The TotalVariation bucket now contains Pinsker's bound, the metric " +
                        "structure with the attained variational characterization, data-processing " +
                        "contraction, Bretagnolle--Huber with the Bhattacharyya coefficient, and " +
                        "the present Hellinger comparison. All divergence units mentioned in this " +
                        "narrative are nats.")),
                    Paragraph(Text(
                        "No Renyi divergence, Hellinger-to-KL bound, equality analysis, or " +
                        "measure-theoretic analogue is claimed."))),
                DescribeRole.Theorem))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
