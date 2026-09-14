using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Expressions;

internal sealed class GuardedArithmeticTermsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded finite arithmetic terms.",
        H("Guarded finite arithmetic terms"),
        Blocks(
            Paragraph(Text("Typed Lean handles carry these statements. Formula projection limitations are "
                + "reported by the canonical Scribe tools; no handwritten formula substitutes for a Lean type. "
                + "The actual real interpretation and the full shared-world expression theorem remain E2.")),
            Describe.Lean(
                DescribeId.Create("grammar"),
                DeclarationHandle.Create(Prefix + "Expr"),
                H("The object language is Mathlib finite term syntax"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Constants and variables occupy different sum leaves. The arithmetic "
                    + "signature has exactly unary negation and binary addition, multiplication and "
                    + "division. Ordered term children retain parentheses. Temporal composition, "
                    + "spatial filters and history queries have no symbols."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("division"),
                DeclarationHandle.Create(Prefix + "allLegal_div"),
                H("Division legality requires both children and its guard"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A division term is structurally legal exactly when both children are "
                    + "structurally legal and their actual evaluation results satisfy the algebra "
                    + "guard. The existential witnesses are those two child results."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("legality"),
                DeclarationHandle.Create(Prefix + "legal_iff_allLegal"),
                H("Existence is exactly structural legality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "AllLegal recursively requires every child and the guard at every division "
                    + "node. Multiplication by a numerical zero and cancellation do not erase an "
                    + "illegal subexpression."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transport"),
                DeclarationHandle.Create(Prefix + "eval_map"),
                H("Proved operation maps commute with finite realization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is a conditional generic transport theorem. mapHom constructs a "
                    + "first-order homomorphism after the primitive operation and guard laws have "
                    + "been supplied as proofs. HomClass.realize_term supplies the finite-term "
                    + "transport. Algebra itself contains only operation data. The integer and "
                    + "rational consumers prove every native premise."))),
                DescribeRole.Theorem)),
        [
        ]));
}
