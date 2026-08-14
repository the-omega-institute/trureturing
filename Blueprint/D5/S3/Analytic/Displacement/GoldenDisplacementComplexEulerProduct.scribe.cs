using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Displacement;

internal sealed class GoldenDisplacementComplexEulerProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen displacement surface lifts to complex parameters and contains the convergent golden Euler germ as its conjugate section.",
        H("Complex Golden Displacement Euler Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complex-displacement-term-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_norm"),
                H("The complex term has the frozen real norm"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Lvert, Sp, F.Id("D"), Caret, Grp(F.Id("C")), Underscore,
                    Grp(F.Id("s"), Comma, F.Id("w")), Open, F.Id("n"), Close, Rvert,
                    Sp, Eq, Sp,
                    F.Id("D"), Underscore, Grp(
                        Operatorname, Grp(F.Id("Re")), Grp(F.Id("s")), Comma,
                        Operatorname, Grp(F.Id("Re")), Grp(F.Id("w"))),
                    Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positive natural bases have zero complex argument, so Mathlib's cpow norm formula "
                        + "removes both imaginary exponent components. The resulting real powers are "
                        + "exactly the already frozen displacement term; the zero index agrees by definition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-displacement-coprime-multiplicativity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_mul_of_coprime"),
                H("The complex term is multiplicative on coprime factors"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Gcd, Grp(F.Id("m"), Comma, F.Id("n")), Sp, Eq, Sp, D(1), Sp,
                    Implies, Sp,
                    F.Id("D"), Caret, Grp(F.Id("C")), Underscore,
                    Grp(F.Id("s"), Comma, F.Id("w")), Open, F.Id("m"), F.Id("n"), Close,
                    Sp, Eq, Sp,
                    F.Id("D"), Caret, Grp(F.Id("C")), Underscore,
                    Grp(F.Id("s"), Comma, F.Id("w")), Open, F.Id("m"), Close,
                    Sp, Cdot, Sp,
                    F.Id("D"), Caret, Grp(F.Id("C")), Underscore,
                    Grp(F.Id("s"), Comma, F.Id("w")), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen hidden product splits on coprime inputs. Mathlib's natural-cast cpow "
                        + "multiplication law splits each positive-base complex power, and the zero cases "
                        + "reduce to the forced coprime unit exactly as in the real displacement surface."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-displacement-absolute-convergence"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_summable"),
                H("The complex displacement series converges absolutely"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Sp,
                    D(0), Sp, Leq, Sp, Operatorname, Grp(F.Id("Re")), Grp(F.Id("s")), Sp,
                    Land, Sp, D(1), Sp, Lt, Sp,
                    Operatorname, Grp(F.Id("Re")), Grp(F.Id("s"), Plus, F.Id("w")), Sp,
                    Implies, Sp,
                    Sum, Underscore, Grp(F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N"))),
                    Lvert, Sp, F.Id("D"), Caret, Grp(F.Id("C")), Underscore,
                    Grp(F.Id("s"), Comma, F.Id("w")), Open, F.Id("n"), Close, Rvert,
                    Sp, Lt, Sp, Infty))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact norm theorem turns the complex absolute-value series into the nonnegative "
                        + "frozen real displacement series at the two real parts. Its established "
                        + "summability therefore supplies convergence with no new analytic estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-displacement-euler-product"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.complex_displacement_euler_product"),
                H("The complex displacement surface has an Euler product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Sp,
                    D(0), Sp, Leq, Sp, Operatorname, Grp(F.Id("Re")), Grp(F.Id("s")), Sp,
                    Land, Sp, D(1), Sp, Lt, Sp,
                    Operatorname, Grp(F.Id("Re")), Grp(F.Id("s"), Plus, F.Id("w")), Sp,
                    Implies, Sp,
                    Prod, Underscore, Grp(F.Id("p"), Sp, F.Text, Grp(F.Id("prime"))),
                    Open, Sum, Underscore, Grp(F.Id("e"), InMacro, Sp, Mathbb, Grp(F.Id("N"))),
                    Open, F.Id("p"), Caret, Grp(Minus, F.Id("s")), Close,
                    Caret, Grp(Operatorname, Grp(F.Id("start")), Grp(F.Id("e"))),
                    Sp, Cdot, Sp,
                    Open, F.Id("p"), Caret, Grp(Minus, F.Id("w")), Close,
                    Caret, Grp(F.Id("e")), Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N"))),
                    F.Id("D"), Caret, Grp(F.Id("C")), Underscore,
                    Grp(F.Id("s"), Comma, F.Id("w")), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pinned Mathlib Euler-product theorem consumes the unit value, zero value, "
                        + "coprime multiplicativity, and absolute summability of the complex term. Its "
                        + "prime-power factors are then rewritten to the displayed Hecke-Mahler monomials."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-beta-substitution-start-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.o5_beta_eq_substitution_start_sub_conjugate"),
                H("The germ exponent is the conjugate-corrected substitution start"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("e"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("o5Beta"), Grp(F.Id("e")), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("start")), Grp(F.Id("e")), Sp, Minus, Sp,
                    F.Id("e"), Sp, Cdot, Sp, Psi, Sp))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public Beatty formula identifies a substitution start with the floor of "
                        + "(e+1) times the golden ratio minus one. Substitution into o5Beta and the "
                        + "identity one minus the golden ratio equals its conjugate give the equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-displacement-prime-germ-section"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_prime_pow_germ_section"),
                H("Prime powers restrict to golden Euler germ monomials"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("e"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("p"), Sp, F.Text, Grp(F.Id("prime")), Sp,
                    Implies, Sp,
                    F.Id("D"), Caret, Grp(F.Id("C")), Underscore,
                    Grp(F.Id("s"), Comma, Minus, Psi, Sp, Cdot, Sp, F.Id("s")),
                    Open, F.Id("p"), Caret, Grp(F.Id("e")), Close, Sp, Eq, Sp,
                    F.Id("p"), Caret, Grp(
                        Minus, F.Id("s"), Sp, Cdot, Sp, F.Id("o5Beta"), Grp(F.Id("e")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the conjugate section, the two prime-power exponents combine by cpow addition. "
                        + "The beta/start identity reduces their sum to minus s times o5Beta e, giving "
                        + "the local golden Euler germ term on every prime power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-displacement-germ-section"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.complex_displacement_germ_section"),
                H("The convergent golden germ is a displacement section"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    D(1), Sp, Lt, Sp, Varphi, Sp, Cdot, Sp,
                    Operatorname, Grp(F.Id("Re")), Grp(F.Id("s")), Sp, Implies, Sp,
                    Prod, Underscore, Grp(F.Id("p"), Sp, F.Text, Grp(F.Id("prime"))),
                    Open, Sum, Underscore, Grp(F.Id("e"), InMacro, Sp, Mathbb, Grp(F.Id("N"))),
                    F.Id("p"), Caret, Grp(
                        Minus, F.Id("s"), Sp, Cdot, Sp, F.Id("o5Beta"), Grp(F.Id("e"))),
                    Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N"))),
                    F.Id("D"), Caret, Grp(F.Id("C")), Underscore,
                    Grp(F.Id("s"), Comma, Minus, Psi, Sp, Cdot, Sp, F.Id("s")),
                    Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The section w = -psi s has real convergence exponent phi times Re(s). Under the "
                        + "strict threshold greater than one, the complex displacement Euler product "
                        + "therefore converges and its local prime terms rewrite to the o5Beta germ."))),
                DescribeRole.Theorem))));
}
