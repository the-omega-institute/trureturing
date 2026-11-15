using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class FiniteRationalConvergentsLengthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithmic length of the rational Euclidean convergent list",
        H("Logarithmic rational convergent length"), Blocks(
            Paragraph(Text("For a rational x, let T(x) be the reciprocal of its fractional part and let den(x) be its positive denominator in lowest terms. The list convergents x includes the integer head. It has one entry at an integer and otherwise has one more entry than convergents T(x). These conventions include zero and negative rationals.")),
            Describe.Lean(DescribeId.Create("logarithmic-length"),
                DeclarationHandle.Create("D5/S1/Depth/ContinuedFractions/FiniteRationalConvergentsLength.convergents_length_log"),
                H("Logarithmic length bound"),
                StatementSource.FromAuthor(Disp(new Formula.Bind(
                    FormulaQuantifier.ForAll, FormulaIdentifier.Create("x"), X("Rat"),
                    new Formula.Relation(C("length", C("convergents", X("x"))),
                        FormulaRelationOperator.LessThanOrEqual,
                        Add(Multiply(Num(2), C("natLog", Num(2), C("den", X("x")))), Num(1)))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/aicyberg2026shor")),
                Blocks(Paragraph(Text("Here natLog(2,d) denotes Lean's Nat.log 2 d, the integer floor of the base-two logarithm for positive d. There are no extra hypotheses on x. Its canonical denominator is always positive; an integer has denominator one and its singleton list meets the bound with equality.")),
                    Paragraph(Text("Strong induction on den(x) separates the integer case, the case where T(x) is an integer, and the case where two recursive steps remain. In the last case the denominator identity for a fractional part gives den(T(T(x))) + den(T(x)) <= den(x). Since den(T(T(x))) < den(T(x)), twice den(T(T(x))) is at most den(x). Monotonicity of the natural logarithm and its multiplication-by-two identity pay for the two list entries removed before the induction hypothesis is applied. The fractional-part argument works for negative x as well."))),
                DescribeRole.Theorem),
            Paragraph(Text("For natural y,Q,N with Q>0, the existing candidates y Q N filters convergents ((y:Rat)/Q) by denominator less than N. Filtering cannot increase length. The existing reduced_den theorem, with s=y, r=Q, gives den((y:Rat)/Q)=Q/gcd(y,Q)<=Q. Apply the displayed theorem at x=(y:Rat)/Q, then Nat.log_mono_right, to obtain length(candidates y Q N)<=2*Nat.log 2 Q+1. No restriction y<Q is needed for this counting consequence. With Q=2^n, positivity of 2^n and Nat.log_pow give length(candidates y (2^n) N)<=2*n+1 for every natural y,n,N, including n=0.")),
            Paragraph(Text("The quantity bounded is the number of list entries, or Euclidean stages. The repeated maps in the list definition have separate work costs. This estimate supplies no bit-operation or gate bound, observable selector, factoring or success-probability theorem, or hardware estimate. The original statements and proofs are due to aicyberg in the cited source.")))));

    private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
}
