using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class FanoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak finite Fano inequality converts conditional entropy in nats into a universal estimator-error bound and opens the S3 Estimation bucket.",
        H("Weak Finite Fano Inequality in Nats"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weak-fano-bounds-conditional-entropy-by-estimation-error"),
                DeclarationHandle.Create("D5/S3/Estimation/Fano.fano_inequality_weak"),
                H("Weak Fano bounds conditional entropy by any estimator's error"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, F.Id("Y"), Comma, Sp, F.Id("X"), Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    F.Id("Y"), Times, Sp, F.Id("X"), To, Sp,
                                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                                    F.Id("g"), Colon, Sp, F.Id("Y"), To, Sp, F.Id("X"), Comma, RowBreak,
                                    F.Id("e"), Colon, Eq,
                                    Sum, Sp, Underscore,
                                    Grp(
                                        F.Id("y"), Comma, Sp, F.Id("x"), Colon, Sp,
                                        F.Id("g"), Open, F.Id("y"), Close, Neq, Sp, F.Id("x")), Sp,
                                    F.Id("p"), Open, F.Id("y"), Comma, Sp, F.Id("x"), Close, Comma, RowBreak,
                                    Open,
                                    Open,
                                    Forall, Sp, F.Id("y"), Comma, Sp, F.Id("x"), Comma, Sp,
                                    D(0), Le, Sp,
                                    F.Id("p"), Open, F.Id("y"), Comma, Sp, F.Id("x"), Close,
                                    Close, Sp, Land, Sp,
                                    Sum, Sp, Underscore, Grp(F.Id("y"), Comma, Sp, F.Id("x")), Sp,
                                    F.Id("p"), Open, F.Id("y"), Comma, Sp, F.Id("x"), Close,
                                    Eq, D(1), Close, Sp, Rightarrow, Sp, RowBreak,
                                    Operatorname, Grp(F.Id("conditionalEntropy")), Open, F.Id("p"), Close,
                                    Le, Sp,
                                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                                    Open, F.Id("b"), Colon, Sp,
                                    Operatorname, Grp(F.Id("Bool")), Close, Mapsto, Sp,
                                    F.Text, Grp(F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp),
                                    F.Id("e"),
                                    F.Text, Grp(Sp, F.Id("else"), Sp),
                                    D(1), Minus, F.Id("e"), Close, Plus, Sp,
                                    F.Id("e"), Sp, Log, Sp, Open,
                                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close, Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Fano's inequality is the standard engine of information-theoretic " +
                                        "converse arguments: a lower estimate for conditional uncertainty, " +
                                        "together with the displayed upper bound, forces a lower bound on the " +
                                        "error probability of every estimator g. This is the repository's first " +
                                        "estimation-theoretic bound and opens that line of development.")),
                                    Paragraph(Text(
                                        "The coordinate order is a design choice, not an accident. The frozen " +
                                        "definition conditionalEntropy p conditions on the first coordinate. " +
                                        "Accordingly, the joint law has type Y x X -> R with Y the observation " +
                                        "and X the estimand, so conditionalEntropy p is already H(X | Y). No " +
                                        "swap, auxiliary definition, or conversion lemma is needed. Choosing " +
                                        "the coordinate order to match the frozen definition is cheaper than " +
                                        "adapting that definition to a preferred order, and the roles of the " +
                                        "coordinates are stated rather than left for the reader to infer.")),
                                    Paragraph(Text(
                                        "The estimator g is arbitrary. The only assumptions on p are " +
                                        "coordinatewise nonnegativity and total mass one, and e is exactly the " +
                                        "total mass of pairs on which g(y) differs from x. All entropy and " +
                                        "divergence quantities in this program use natural logarithms and are " +
                                        "therefore measured in nats.")),
                                    Paragraph(Text(
                                        "The library search found the existing declaration " +
                                        "Quantum.CloningMachine.binaryEntropyBits and deliberately did not use " +
                                        "it. That declaration is built from Real.logb 2 and is measured in " +
                                        "bits, whereas shannonEntropy and every divergence in this program are " +
                                        "measured in nats. Mixing the two would silently corrupt Fano's " +
                                        "constant. The binary term is instead written directly as the " +
                                        "nats-valued shannonEntropy of the Bool law (e, 1-e). Thus no new " +
                                        "definition is introduced and no unit conversion is hidden. Finding " +
                                        "an existing declaration and correctly declining to use it is part of " +
                                        "the record, not an omission.")),
                                    Paragraph(Text(
                                        "The claimed form is deliberately weak: its cardinality term is " +
                                        "log(card X), not the sharper log(card X - 1). The strong refinement " +
                                        "must split off the singleton case, where Real.log 0 appears and Lean " +
                                        "totalizes it to zero. Claiming the sharp form without that split would " +
                                        "make the argument rest on totalization rather than analysis. A " +
                                        "compiled degenerate witness with Y = X = Unit records that the error, " +
                                        "conditional entropy, and binary entropy are all zero, and that " +
                                        "log(card X - 1) is exactly the totalized Real.log 0 = 0.")),
                                    Paragraph(Text(
                                        "The proof first rewrites conditional entropy as a finite sum of " +
                                        "log-ratios. It then applies the repository's frozen " +
                                        "log_sum_inequality separately to the correctly estimated mass and the " +
                                        "misestimated mass before recombining them. The log-sum inequality was " +
                                        "deposited two waves earlier for convexity of divergence; it is now " +
                                        "load-bearing for an estimation bound in a different bucket.")),
                                    Paragraph(Text(
                                        "The theorem is not vacuous. Take Y = Unit, X = Bool, the uniform joint " +
                                        "law, and the constant-false estimator. Then e = 1/2, the conditional " +
                                        "entropy is log 2, and the right side is (3/2) log 2, so the inequality " +
                                        "is strict. The checks that neither rfl nor simp closes the general " +
                                        "bound were compiled as fail_if_success obligations.")),
                                    Paragraph(Text(
                                        "This document opens the Estimation bucket at stratum S3. It claims no " +
                                        "sharp log(card X - 1) form, no converse direction, no minimax or " +
                                        "sample-complexity corollary, and no measure-theoretic analogue. The " +
                                        "scope remains finite and nats-valued throughout."))),
                DescribeRole.Theorem
            ))));
}
