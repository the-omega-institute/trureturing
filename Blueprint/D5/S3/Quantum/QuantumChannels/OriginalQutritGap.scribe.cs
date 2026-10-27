using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class OriginalQutritGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The commutator controls the original qutrit channel on the full complex traceless space.",
        H("The original two-swap channel"),
        Blocks(Describe.Lean(DescribeId.Create("original-two-sided"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/OriginalQutritGap.original_two_sided"),
            H("Both bounds include commuting installations"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("U exchanges coordinates 1 and 2, W exchanges 0 and 1, "
                    + "and xi=(1,1,1)/sqrt(3). Put Pxi=xi xi*, D(X)=(X+W X W*)/2 "
                    + "and Lambda(X)=U D(X) U*. For every complex unitary 3 by 3 matrix N, "
                    + "Theta_N=Lambda squared composed with Ad_N composed with Lambda squared. "
                    + "The carrier H0 consists of all complex trace-zero 3 by 3 matrices. "
                    + "Its Hilbert-Schmidt norm is transported by CartesianVariance.vectorize; "
                    + "r_N is the induced operator norm of Theta_N on H0. "
                    + "Delta_N is the squared Hilbert-Schmidt norm of N Pxi-Pxi N.")),
                Paragraph(Text("The unit vector v has zero diagonal and all six off-diagonal "
                    + "entries 1/sqrt(6). The exact energy identity for the original A=Lambda squared "
                    + "gives contraction by at most one half on the orthogonal complement of v in H0. "
                    + "Both A and its adjoint fix v. For R=Ad_N and eta squared equal to "
                    + "1-abs(inner(v,Rv)) squared, the two losses in A R A yield "
                    + "eta squared/3 at most 1-r_N squared at most eta squared. "
                    + "The same N occurs in the middle action and in the commutator.")),
                Paragraph(Text("The centered identity Pxi=I/3+(sqrt(6)/3)v connects these estimates "
                    + "to the original projection. Hermiticity makes t=inner(v,Rv) real; "
                    + "positivity of trace(Pxi N Pxi N*) gives t at least -1/2. "
                    + "Direct unitary norm invariance gives "
                    + "delta_N=(4/3)(1-t), hence 0 at most delta_N at most 2 and "
                    + "eta squared=(3 delta_N/4)(2-3 delta_N/4). "
                    + "These identities include delta_N=0 and N xi orthogonal to xi. "
                    + "No division by delta_N or exclusion of either endpoint is used.")),
                Paragraph(Text("The direct scalar consequence is r_N to the power n at most "
                    + "(1-delta_N/8) to the power n/2, at most exp(-n delta_N/16), for integers n at least zero. "
                    + "This supplies a decay envelope for a fixed installed N. "
                    + "Physical consumers still require the original memoryless lift, exact law (101.5), "
                    + "the same installed N and J J N J J chronology, coherent archive access, "
                    + "two-sided archive alignment and complete late measurements with three outcomes. "
                    + "The original block still uses four instruments, one N and four records. "
                    + "The population statement restricted to d different from 2/3 remains separate; "
                    + "d=2/3 stays allowed in the universal matrix theorem. "
                    + "The estimate supplies no preparation-time lower bound, calibration procedure, "
                    + "common physical realization or uniform finite cost over all installations."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Frac(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Statement()
    {
        var n = F.Id("N");
        var delta = Call("delta", n);
        var gap = Seq(Num(1), Minus, Pow(Call("r", n), Num(2)));
        var lower = new Formula.Relation(Frac(delta, Num(8)),
            FormulaRelationOperator.LessThanOrEqual, gap);
        var upper = new Formula.Relation(gap, FormulaRelationOperator.LessThanOrEqual,
            new Formula.Binary(Frac(Num(3), Num(2)), FormulaBinaryOperator.Multiply, delta));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("N"), Call("ComplexUnitaryMatrix", Num(3)),
            new Formula.Logic(lower, FormulaLogicOperator.And, upper)));
    }
}
