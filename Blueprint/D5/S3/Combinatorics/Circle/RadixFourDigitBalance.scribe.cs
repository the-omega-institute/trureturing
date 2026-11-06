using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class RadixFourDigitBalanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/RadixFourDigitBalance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal even-label trace of every radix-four seed has the full binomial balance spectrum.",
        H("Radix-four literal even-trace spectrum"),
        Blocks(
            Paragraph(Text(
                "Fix n>0. The physical labels are the original evenLabel i in Fin(2*n), "
                + "and evenTrace(n,t) is the integer sum of SourceWidth.actualSource(2*n,t,evenLabel i) "
                + "over i:Fin(n). The seed is the natural t reduced only by the literal modulus "
                + "4^n-1; every distinct state t:Fin(4^n-1), including zero and nonunits, remains "
                + "a separate seed.")),
            Paragraph(Text(
                "The digit-balance law uses the exact filters over i:Fin(n): digits equal to one "
                + "minus digits equal to two in the fixed-length radix-four expansion of "
                + "t mod (4^n-1). Its equality is in the integers and is tied to the actual physical "
                + "even labels; no modular-zero, unit-only, quotient-label, or full-J replacement is used.")),
            Describe.Lean(
                DescribeId.Create("actual-even-digit-balance"),
                DeclarationHandle.Create(Prefix + "actual_even_digit_balance"),
                H("Every natural seed has the literal even-label digit balance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all n>0 and every natural t, 3*evenTrace(n,t) equals modulus(2*n) times "
                    + "the integer cardinality difference of the digit-one and digit-two filters. "
                    + "The statement retains the exact original telescope and source expression."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("even-trace-seed-spectrum"),
                DeclarationHandle.Create(Prefix + "even_trace_seed_spectrum"),
                H("All natural balance fibres have binomial size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every n>0 and every r:Nat, the Fin(4^n-1) seeds whose literal integer "
                    + "trace satisfies 3*evenTrace(n,t.val)=modulus(2*n)*((r:Int)-(n:Int)) have "
                    + "cardinality Nat.choose(2*n,r), after adding exactly one when r=n. The all-three "
                    + "word is the sole omitted endpoint and is restored only in the central fibre; "
                    + "r=0, r=n, r=2*n and r>2*n remain inside the same formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-even-trace-seed-count"),
                DeclarationHandle.Create(Prefix + "zero_even_trace_seed_count"),
                H("The central zero-trace seed count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original central law is retained exactly: the number of distinct residue seeds "
                    + "t:Fin(4^n-1) with literal evenTrace(n,t.val)=0, plus one for the all-three word, "
                    + "equals Nat.choose(2*n,n). This is obtained by specializing the full spectrum and "
                    + "does not count physical zero subsets of one source."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The proof uses Mathlib's finFunctionFinEquiv for the exact radix word/value bijection, "
                + "an explicit labelled bit-pair equivalence into Fin(2*n), and powersetCard for every "
                + "natural r. The centered representative and the actualSource recurrence stay tied to "
                + "the existing SourceWidth and radix-four support laws. This Scribe records the owning "
                + "scope and parameter correspondence; it is not a substitute for the current Lean "
                + "kernel report or for the companion Reg audit."))), []));
}
