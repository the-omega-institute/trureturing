using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class MinimalPositiveRepairDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S1/Eigenstructure/MinimalPositiveRepair.minimal_positive_repair";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp positive repair of the Fibonacci eigenform, with the corrected uniqueness scope.",
        H("Minimal Positive Repair"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimal-positive-repair"),
            DeclarationHandle.Create(Handle),
            H("Sharp norm bound, attainment, and spectral minimality"),
            StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Call("PosSemidef", F.Id("R")), Sp, Land, Sp,
                    Call("PosSemidef", Seq(F.Id("F"), Sp, Plus, Sp, F.Id("R"))),
                    Sp, Rightarrow, Sp,
                    new Formula.Subscript(
                        Seq(Lvert, Sp, F.Id("R"), Sp, Rvert), F.Id("op")),
                    Sp, Ge, Sp,
                    Varphi, Caret, Grp(Minus, D(1)), Comma),
                Seq(F.Id("Rmin"), Sp, Eq, Sp, Varphi, Caret, Grp(Minus, D(1)),
                    Sp, Cdot, Sp, new Formula.Subscript(F.Id("P"), Minus), Comma),
                Seq(F.Id("F"), Sp, Plus, Sp, F.Id("Rmin"), Sp, Eq, Sp,
                    Varphi, Sp, Cdot, Sp, new Formula.Subscript(F.Id("P"), Plus), Comma),
                Seq(Exists, Sp, F.Id("Ralt"), Comma, Sp,
                    F.Id("Ralt"), Sp, Neq, Sp, F.Id("Rmin"), Sp, Land, Sp,
                    new Formula.Subscript(
                        Seq(Lvert, Sp, F.Id("Ralt"), Sp, Rvert), F.Id("op")),
                    Sp, Eq, Sp, Varphi, Caret, Grp(Minus, D(1)), Dot),
            ]))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The Fibonacci form is represented in its expanding and contracting "
                        + "eigenbasis. Positivity on the contracting coordinate forces every "
                        + "feasible repair to have operator norm at least phi inverse.")),
                Paragraph(Text(
                    "The negative-part repair attains the bound, leaves phi times the expanding "
                        + "projection, is positive semidefinite, and has rank one. The proof uses "
                        + "Mathlib's L2 matrix operator norm rather than an entrywise norm.")),
                Paragraph(Text(
                    "The source's unrestricted uniqueness assertion is false: phi inverse times "
                        + "the identity is a distinct feasible repair with the same norm. The Lean "
                        + "theorem records this counterexample and proves uniqueness only for the "
                        + "coefficientwise least repair diagonal in the Fibonacci eigenbasis."))),
            DescribeRole.Theorem))));
}
