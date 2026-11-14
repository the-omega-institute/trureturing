using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;
internal sealed class ShorCountingMarginalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual padded modular counting-register marginal", H("Actual padded modular counting-register marginal"), Blocks(
            Describe.Lean(DescribeId.Create("actual-marginal"),
                DeclarationHandle.Create("D5/S3/Quantum/ShorCountingMarginal.shor_qpe_probability_mixture"),
                H("Actual-input counting marginal"), StatementSource.FromAuthor(Disp(All(Eq(Marginal(X("y")), Mul(Div(Num(1), C("period", X("c"))), Sum("s", C("Fin", C("period", X("c"))), C("probability", Q(), Div(C("val", X("s")), C("period", X("c"))), X("y"))))), ("c", X("Parameters")), ("n", X("Nat")), ("y", C("Fin", Q()))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/aicyberg2026shor")),
                Blocks(Paragraph(Text("The target input is the computational basis vector at coordinate one. Multiplication by the coprime base permutes residues below the modulus and fixes padding. The control width n and target width are independent. The left side sums squared complex coordinate norms over every target coordinate at the specified counting outcome. The right side is the uniform mixture over all order eigenphases. No divisibility of the period into the power-of-two control dimension is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized"),
                DeclarationHandle.Create("D5/S3/Quantum/ShorCountingMarginal.shor_distribution_normalized"),
                H("Normalization over all counting outcomes"), StatementSource.FromAuthor(Disp(All(Eq(Sum("y", C("Fin", Q()), Marginal(X("y"))), Num(1)), ("c", X("Parameters")), ("n", X("Nat"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/aicyberg2026shor")),
                Blocks(Paragraph(Text("Summing the actual marginal over all counting outcomes gives one, including n equal to zero. The proof consumes the actual-input mixture and the normalized phase kernels. It does not condition on a target-register measurement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pointwise-nearest"),
                DeclarationHandle.Create("D5/S3/Quantum/ShorCountingMarginal.shor_mixture_peak_lower_bound"),
                H("Pointwise circular nearest-grid marginal bound"), StatementSource.FromAuthor(Disp(All(Imp(C("Nearest", Q(), Div(C("val", X("s")), C("period", X("c"))), X("b")), LE(Mul(Div(Num(1), C("period", X("c"))), Div(Num(4), Pow(X("pi"), Num(2)))), Marginal(X("b")))), ("c", X("Parameters")), ("n", X("Nat")), ("s", C("Fin", C("period", X("c")))), ("b", C("Fin", Q()))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/aicyberg2026shor")),
                Blocks(Paragraph(Text("For any selected order eigenphase and any grid label within circular distance one over twice the control dimension, the actual marginal is at least one over the period times four over pi squared. Either midpoint tie is allowed. Distinct selected phases can share a grid label, so this pointwise result alone is not an aggregate-event success theorem."))), DescribeRole.Theorem),
            Paragraph(Text("Chapter 15 correspondence: Q is two to the control width; D is two to the independently chosen target width; r is the multiplicative order of the base modulo the modulus. Fin Q and ZMod Q are related by the pinned ZMod.finEquiv ring equivalence, using the least nonnegative representative. The modulus is at least two, the base is coprime to it, and the modulus fits in D. The supplied period positivity follows from coprimality.")),
            Paragraph(Text("The sums displayed here use sum(i, Fin m, f) for summation over the indicated finite index, and runQPEAt for coordinate evaluation of runQPE. The normalized positive Fourier transform in Chapter 15 is scale Q times the unnormalized negative-exponent ZMod.dft at the negated output coordinate. The supplied inverseQFT is scale Q times that DFT at the unreflected output. Thus using the positive transform for the final sweep reflects the grid label. At an output b satisfying the supplied circular nearest-grid condition for s/r, the positive final Fourier map has the same target vector at finEquiv.symm applied to negative finEquiv(b); the same pointwise bound holds at that reflected label. A sign change cannot be dropped. The uniform control preparation and final Fourier map each contribute an inverse square-root factor, giving the inverse-Q amplitude prefactor.")),
            Paragraph(Text("The actual circuit state is runQPE c.modularOperator n c.input. Its input has amplitude one precisely at target label one and zero elsewhere. At a fixed output y the complete target sum is normSquared of that target vector, and summing over y is the normalized distribution. registerPerm is the residue permutation extended by identity to the padding; no arbitrary joint state or conditioned posterior comb is substituted.")),
            Paragraph(Text("The marginal, normalization and pointwise circular nearest-grid estimate are the supported mathematical scope. Aggregate success probability, coprime sampling, continued-fraction recovery, factoring, gate or bit complexity, arbitrary control dimensions, conditioned posterior-comb bounds and hardware claims require separate results.")))));
    private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula Eq(Formula x, Formula y) => DefinitionDsl.Equal(x, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula LE(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Sum(string i, Formula t, Formula f) => C("sum", X(i), t, f);
    private static Formula All(Formula f, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            f = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, f);
        return f;
    }
    private static Formula Q() => Pow(Num(2), X("n"));
    private static Formula Marginal(Formula y) => Sum("t", C("Fin", C("dimension", X("c"))), C("normSq", C("runQPEAt", C("modularOperator", X("c")), X("n"), C("input", X("c")), y, X("t"))));
}
