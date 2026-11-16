using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;
internal sealed class FiniteRationalConvergentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Executable finite rational lists and exact real convergent correspondence",
        H("Finite rational convergents"), Blocks(
            Paragraph(Text("For any rational x, convergents x starts with its integer floor. If its fractional part is zero the list stops there. Otherwise it recursively computes the list at the reciprocal fractional part, then adds the floor to the reciprocal of each recursive entry. The positive reduced denominator strictly decreases at each recursive call. This construction accepts negative rationals, zero and integers; no positive-input hypothesis is imposed. Well-founded recursion makes the list finite; the separate logarithmic length theorem bounds its number of entries.")),
            Paragraph(Text("The observable list candidates y Q N filters convergents of the rational y / Q by reduced denominator strictly less than N. Its only inputs are natural numbers y, Q and N. It has no order or spectral-numerator input. Rational division totalizes the definition also at Q equal to zero, while the recovery theorem uses a positive resolved clock. reduced s r denotes the rational s / r.")),
            Describe.Lean(DescribeId.Create("tail-denominator-decrease"),
                DeclarationHandle.Create("D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents.tail_den_lt"),
                H("Reciprocal-tail denominator decrease"),
                StatementSource.FromAuthor(Disp(All(Imp(
                    new Formula.Not(Eq(C("fract", X("x")), Num(0))),
                    Rel(C("den", C("inv", C("fract", X("x")))), FormulaRelationOperator.LessThan,
                        C("den", X("x")))), ("x", X("Rat"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/aicyberg2026shor")),
                Blocks(Paragraph(Text("For a nonzero fractional part, the reciprocal's denominator is the fractional numerator. That nonnegative numerator is strictly below the original denominator because the fractional part is less than one. This decrease both terminates the list recursion and supports the two-step induction for its logarithmic length bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-list-correspondence"),
                DeclarationHandle.Create("D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents.mem_convergents_iff"),
                H("Exact list correspondence"),
                StatementSource.FromAuthor(Disp(All(new Formula.Logic(
                    Rel(X("z"), FormulaRelationOperator.MemberOf, C("convergents", X("x"))), FormulaLogicOperator.Iff,
                    new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("k"), X("Nat"),
                        Eq(C("realConvergent", C("toReal", X("x")), X("k")), X("z")))),
                    ("x", X("Rat")), ("z", X("Rat"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/aicyberg2026shor")),
                Blocks(Paragraph(Text("In the display, realConvergent denotes Mathlib's Real.convergent and natDiv denotes natural-number division. Both directions follow the Euclidean denominator descent. At an integer, all totalized real convergents repeat that integer. At a noninteger, the head is the zeroth convergent, and the reciprocal-tail recurrence transports each tail index to its successor. Thus repeated terminal real convergents are represented by a single finite-list entry. The consuming recovery proof uses this equivalence to turn the index supplied by Mathlib's Legendre theorem into actual list membership."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reduced-denominator"),
                DeclarationHandle.Create("D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents.reduced_den"), H("Reduced denominator"),
                StatementSource.FromAuthor(Disp(All(Imp(Rel(Num(0), FormulaRelationOperator.LessThan, X("r")),
                    Eq(C("den", C("reduced", X("s"), X("r"))), C("natDiv", X("r"), C("gcd", X("s"), X("r"))))),
                    ("s", X("Nat")), ("r", X("Nat"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/aicyberg2026shor")),
                Blocks(Paragraph(Text("The positive-denominator formula directly uses the pinned rational normalization laws. It remains valid at s equal to zero and r equal to one. The denominator divides r, is at most r, and equals r when s and r are coprime. These consequences are used inside the conditional Shor recovery proof."))), DescribeRole.Theorem),
            Paragraph(Text("Mathlib supplies the real convergent recurrence and Legendre approximation theorem. The finite-list correspondence connects that recurrence with executable rational Euclidean descent.")))));
    private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula Eq(Formula x, Formula y) => DefinitionDsl.Equal(x, y);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula All(Formula f, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            f = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, f);
        return f;
    }
}
