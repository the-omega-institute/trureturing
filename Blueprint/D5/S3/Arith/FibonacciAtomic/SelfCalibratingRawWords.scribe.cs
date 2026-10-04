using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SelfCalibratingRawWordsDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every literal Fibonacci and swap word has a two-sided signed coefficient bound.",
        H("Signed Bounds for Chronological Fibonacci Words"),
        Blocks(
            Paragraph(Text(
                "False is M with rows (0,1),(1,1); true is J with rows (0,1),(1,0). "
                + "E(w) evaluates a finite chronological Boolean list. E(empty)=I and "
                + "E(p followed by q)=E(q)E(p). n is the literal list length.")),
            Paragraph(Text(
                "D=E(w)22-E(w)11. For n>=0 let L(n)=(n-1)/2 with natural truncated "
                + "subtraction and integer division, and H(n)=(n+1)/2. e is either "
                + "offdiagonal entry separately, not their sum or minimum.")),
            Describe.Lean(DescribeId.Create("self-calibrating-raw-word-signed-bound"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/SelfCalibratingRawWords.raw_word_signed_bound"),
                H("Both signs, both denominators, and integral chronology"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("w"), Comma, Sp,
                    Minus, Call("L", F.Id("n")), F.Id("e"), Sp, Leq, Sp, F.Id("D"),
                    Sp, Leq, Sp, Call("H", F.Id("n")), F.Id("e"), Sp, Land, Sp,
                    Call("IntegralChronology", F.Id("w")), Sp, Land, Sp,
                    Call("AlternatingFormulas", F.Id("w")), Sp, Land, Sp,
                    Call("ShortestShearPrefix", F.Id("w"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The bound holds for every raw list, including adjacent JJ, MM, "
                        + "and empty lists. IntegralChronology means every entry is nonnegative, "
                        + "det(E(w))=(-1)^n, and E(w followed by q)=E(q)E(w) for every q. "
                        + "A zero chosen offdiagonal forces D=0; no division is used.")),
                    Paragraph(Text("For alternating words of length 2j, starting with M gives "
                        + "rows (1,j),(0,1), and starting with J gives rows (1,0),(j,1). "
                        + "At length 2j+1 the corresponding rows are (0,1),(1,j+1) and "
                        + "(j,1),(1,0). These formulas include j=0.")),
                    Paragraph(Text("An equal JJ pair removes two letters without changing its "
                        + "matrix. An MM pair uses M squared = M+I, giving a sum of two "
                        + "strictly shorter generated words. Their signed inequalities widen "
                        + "to the original length and add separately for each denominator. "
                        + "An exhaustive adjacent-pair decomposition leaves the alternating "
                        + "cases. Algebraic rewrites do not refund actions already executed.")),
                    Paragraph(Text("For either shear U^k or V^k, with k>0, every literal "
                        + "representation has length at least 2k. Remove JJ pairs. A remaining "
                        + "MM pair gives a strictly positive matrix: each surrounding "
                        + "nonnegative invertible word has a nonzero row and column, and "
                        + "M squared is strictly positive. This contradicts the shear zero. "
                        + "The exhaustive alternating forms then force even length 2k."))),
                DescribeRole.Theorem))));
}
