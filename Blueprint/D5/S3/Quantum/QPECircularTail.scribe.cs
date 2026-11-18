using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;
internal sealed class QPECircularTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Single-phase circular QPE tail", H("Single-phase circular QPE tail"), Blocks(
            Describe.Lean(DescribeId.Create("circular-tail"),
                DeclarationHandle.Create("D5/S3/Quantum/QPECircularTail.qpe_circular_tail_le"),
                H("Uniform mass outside a circular window"),
                StatementSource.FromAuthor(Disp(All(Imp(
                    new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, X("rho")),
                    LE(TailSum(),
                        Add(Div(Num(1), Mul(Mul(Num(2), Q()), X("rho"))),
                            Div(Num(1), Mul(Num(2), Pow(Mul(Q(), X("rho")), Num(2))))))),
                    ("t", X("Nat")), ("phi", X("Real")), ("rho", X("Real"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qpetail")),
                Blocks(
                    Paragraph(Text("Q is two to the natural width t. The sum is over exactly the labels whose circular distance is at least rho. circularDistance(phi, j, Q) is the norm of the image of the real number phi minus j.val / Q in UnitAddCircle, the real additive circle modulo one. All divisions in the displayed bound are real. The only premise is positivity of rho; phi is any real number.")),
                    Paragraph(Text("The probability is exactly QuantumPhaseEstimationGeneral.probability Q phi j, the squared norm of the existing inverse-Fourier phase amplitude. That amplitude is one over Q times the finite sum of exp(2 pi i k.val (phi - j.val / Q)). The normalization and phase convention are those of ShorCountingMarginal. Comparing with a positive final Fourier transform requires reflecting the output label modulo Q.")),
                    Paragraph(Text("Subtracting the nearest integer from each raw phase error gives a representative of absolute value at most one half. Its scaled error is Q phi minus an integer lift of j; reduction modulo Q proves that distinct labels have distinct lifts. The geometric amplitude has norm at most one over twice Q times the positive circular distance. Squaring and summing reduces the event to a finite two-sided reciprocal-square tail. Splitting about the floor of the center bounds each side by its first reciprocal-square term plus a telescoping reciprocal tail.")),
                    Paragraph(Text("The bad event includes equality at rho, so the complementary good window has distance strictly less than rho. The estimate includes t equal to zero, integer-shifted and negative phases, wraparound, either midpoint representative, empty events and every positive radius, including radii larger than one half. No nearest-outcome, order or coprimality assumption is used. The bound describes one phase register at one eigenphase. Aggregate Shor success, eigenphase mixtures, repeated trials, continued-fraction recovery, factoring and hardware performance require separate results."))),
                DescribeRole.Theorem))));
    private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula TailSum() => Seq(
        new Formula.Subscript(Sum, Seq(X("j"), Colon, C("Fin", Q()), Comma,
            LE(X("rho"), Distance(X("j"))))), Sp,
        C("probability", Q(), X("phi"), X("j")));
    private static Formula Q() => Pow(Num(2), X("t"));
    private static Formula Distance(Formula j) => C("circularDistance", X("phi"), j, Q());
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula LE(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula All(Formula f, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            f = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, f);
        return f;
    }
}
