using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Displacement;

internal sealed class GoldenDisplacementEulerProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The hidden golden-substitution product is multiplicative on coprimes and yields an absolutely convergent two-variable Euler product.",
        H("Golden Displacement Euler Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-hidden-product-on-prime-powers"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_prime_pow"),
                H("The hidden product has an exact prime-power formula"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("e"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("p"), Sp, F.Text, Grp(F.Id("prime")), Sp, Implies, Sp,
                    F.Id("nS"), Open, F.Id("p"), Caret, Grp(F.Id("e")), Close,
                    Sp, Eq, Sp, F.Id("p"), Caret, Grp(
                        Operatorname, Grp(F.Id("start")), Open, F.Id("e"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A prime power has factorization support at one prime with exponent e. Evaluating "
                        + "the finite product defining nS therefore replaces that lone exponent by its "
                        + "golden substitution start, while the zero-exponent case reduces to the unit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-hidden-product-coprime-multiplicativity"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_mul_of_coprime"),
                H("The hidden product is multiplicative on coprime factors"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Gcd, Open, F.Id("m"), Comma, F.Id("n"), Close, Sp, Eq, Sp, D(1),
                    Sp, Implies, Sp,
                    F.Id("nS"), Open, F.Id("m"), F.Id("n"), Close, Sp, Eq, Sp,
                    F.Id("nS"), Open, F.Id("m"), Close, Sp, Cdot, Sp,
                    F.Id("nS"), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coprime natural numbers have disjoint prime-factorization supports. The factorization "
                        + "of their product is the sum of the two exponent maps, so the finite product for "
                        + "nS splits across those disjoint supports into the product of the two nS values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-hidden-product-not-completely-multiplicative"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_not_completelyMultiplicative"),
                H("The hidden product is not completely multiplicative"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("p"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("p"), Sp, F.Text, Grp(F.Id("prime")), Sp, Land, Sp,
                    F.Id("nS"), Open, F.Id("p"), Caret, Grp(D(2)), Close, Sp, Neq, Sp,
                    F.Id("nS"), Open, F.Id("p"), Close, Caret, Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the prime two, one substitution exponent is two but the substitution exponent "
                        + "at level two is three rather than four. The prime-power formula consequently "
                        + "gives nS of four as eight, whereas the square of nS of two is sixteen."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-hidden-product-divisibility"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dvd_nS"),
                H("Every nonzero input divides its hidden product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("n"), Neq, D(0), Sp, Implies, Sp,
                    Exists, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("nS"), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    F.Id("n"), F.Id("k")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The golden substitution start of every exponent is at least that exponent. Comparing "
                        + "the prime-factorization exponents of n and nS n therefore proves divisibility "
                        + "coordinate by coordinate; nonzeroness supplies the factorization criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-term-coprime-multiplicativity"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_mul_of_coprime"),
                H("The displacement term is multiplicative on coprime factors"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Gcd, Open, F.Id("m"), Comma, F.Id("n"), Close, Sp, Eq, Sp, D(1),
                    Sp, Implies, Sp,
                    F.Id("D"), Underscore, Grp(F.Id("s"), Comma, F.Id("w")),
                    Open, F.Id("m"), F.Id("n"), Close, Sp, Eq, Sp,
                    F.Id("D"), Underscore, Grp(F.Id("s"), Comma, F.Id("w")),
                    Open, F.Id("m"), Close, Sp, Cdot, Sp,
                    F.Id("D"), Underscore, Grp(F.Id("s"), Comma, F.Id("w")),
                    Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonzero coprime inputs, coprime multiplicativity of nS and the real-power law "
                        + "split both factors in the displacement term. If either input is zero, coprimality "
                        + "forces the other to be one, and the explicitly defined zero and unit values close the case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-absolute-convergence"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_summable"),
                H("The displacement series converges absolutely"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Sp, Leq, Sp, F.Id("s"), Sp, Land, Sp,
                    D(1), Sp, Lt, Sp, F.Id("s"), Plus, F.Id("w"), Sp, Implies, Sp,
                    Sum, Underscore, Grp(F.Id("n"), InMacro, Mathbb, Grp(F.Id("N"))),
                    Lvert, Sp, F.Id("D"), Underscore, Grp(F.Id("s"), Comma, F.Id("w")),
                    Open, F.Id("n"), Close, Rvert, Sp, Lt, Sp, Infty))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Divisibility gives n at most nS n. When s is nonnegative, raising both quantities "
                        + "to the nonpositive exponent minus s bounds each displacement term by n to "
                        + "the power minus s minus w. The convergent natural-power series supplies domination."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-prime-power-local-term"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_prime_pow"),
                H("Prime powers give the Hecke-Mahler local monomials"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("e"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("p"), Sp, F.Text, Grp(F.Id("prime")), Sp, Implies, Sp,
                    F.Id("D"), Underscore, Grp(F.Id("s"), Comma, F.Id("w")),
                    Open, F.Id("p"), Caret, Grp(F.Id("e")), Close, Sp, Eq, Sp,
                    Open, F.Id("p"), Caret, Grp(Minus, F.Id("s")), Close,
                    Caret, Grp(Operatorname, Grp(F.Id("start")), Open, F.Id("e"), Close),
                    Sp, Cdot, Sp,
                    Open, F.Id("p"), Caret, Grp(Minus, F.Id("w")), Close,
                    Caret, Grp(F.Id("e"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substituting the exact nS prime-power formula into the displacement definition "
                        + "separates the real powers of p. The real-power multiplication identities then "
                        + "rewrite the result as the local two-variable monomial indexed by the exponent e."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-euler-product"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.displacement_euler_product"),
                H("The displacement surface has an Euler product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Sp, Leq, Sp, F.Id("s"), Sp, Land, Sp,
                    D(1), Sp, Lt, Sp, F.Id("s"), Plus, F.Id("w"), Sp, Implies, Sp,
                    Prod, Underscore, Grp(F.Id("p"), Sp, F.Text, Grp(F.Id("prime"))),
                    Open, Sum, Underscore, Grp(F.Id("e"), InMacro, Mathbb, Grp(F.Id("N"))),
                    Open, F.Id("p"), Caret, Grp(Minus, F.Id("s")), Close,
                    Caret, Grp(Operatorname, Grp(F.Id("start")), Open, F.Id("e"), Close),
                    Sp, Cdot, Sp,
                    Open, F.Id("p"), Caret, Grp(Minus, F.Id("w")), Close,
                    Caret, Grp(F.Id("e")), Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("n"), InMacro, Mathbb, Grp(F.Id("N"))),
                    F.Id("D"), Underscore, Grp(F.Id("s"), Comma, F.Id("w")),
                    Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pinned mathlib Euler-product theorem applies to the displacement term using its "
                        + "unit value, zero value, coprime multiplicativity, and absolute summability. A "
                        + "termwise rewrite by the prime-power formula identifies every local factor with "
                        + "the displayed two-variable Hecke-Mahler series."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-zeta-cross-section"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.zeta_section"),
                H("The zero-displacement cross-section is the zeta series"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("w"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Sum, Underscore, Grp(F.Id("n"), InMacro, Mathbb, Grp(F.Id("N"))),
                    F.Id("D"), Underscore, Grp(D(0), Comma, F.Id("w")),
                    Open, F.Id("n"), Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(
                        F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                        F.Id("n"), Neq, D(0)),
                    F.Id("n"), Caret, Grp(Minus, F.Id("w"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Setting s to zero makes the hidden-product factor equal one at every nonzero n, "
                        + "while the displacement definition keeps the zero term equal to zero. Termwise "
                        + "congruence therefore identifies the resulting series with the ordinary zeta "
                        + "Dirichlet series over positive natural numbers."))),
                DescribeRole.Theorem))));
}
