using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class OriginalQutritWashDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The installed DU wash has an explicit Hilbert-Schmidt decay rate.",
        H("An explicit rate for the fixed control"),
        Blocks(Describe.Lean(DescribeId.Create("explicit-wash-bound"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/OriginalQutritWash.explicit_wash_bound"),
            H("The complete complex matrix domain and all natural powers"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("U exchanges coordinates 1 and 2, W exchanges 0 and 1, "
                    + "D=diag(1,1,-1), and N=DU is the single installed control. "
                    + "Lambda=Ad_U composed with (id+Ad_W)/2 and "
                    + "Theta=Lambda squared composed with Ad_N composed with Lambda squared. "
                    + "HS(X) is the norm of CartesianVariance.vectorize 3 X in the complex "
                    + "Euclidean space indexed by pairs of qutrit coordinates. "
                    + "It is the complex Frobenius norm. X ranges over every complex trace-zero "
                    + "3 by 3 matrix; no Hermiticity assumption is imposed on this clause. "
                    + "The powers are raw repeated applications of Theta, including the identity at n=0. "
                    + "A density sigma means actual positive semidefiniteness and trace one.")),
                Paragraph(Text("Let A=Lambda squared and let v have zero diagonal and "
                    + "off-diagonal entries 1/sqrt(6). This is the normalized centered P_xi line. "
                    + "A fixes v, preserves its perpendicular complement in the trace-zero space, "
                    + "and contracts that complement by at most one half. For K=Ad_N, "
                    + "inner(v,Kv)=-1/3. The component of the adjoint image of v perpendicular "
                    + "to v has squared norm 8/9. Cauchy-Schwarz bounds its pairing with z=Ay. "
                    + "Writing X=alpha v+y yields "
                    + "HS(AKA X) squared at most (5/12) abs(alpha) squared "
                    + "+(19/48) HS(y) squared, hence at most (5/12) HS(X) squared. "
                    + "Since sqrt(5/12) is below 2/3, repeated application proves the power estimate.")),
                Paragraph(Text("The same actual map preserves trace and fixes the identity. "
                    + "It therefore commutes with centering a density at I/3, including under iteration. "
                    + "The density purity bound and the Hilbert-Schmidt centering identity give "
                    + "HS(sigma-I/3) squared at most 2/3, giving the stated prefactor. "
                    + "The density statement at n=0 is part of the result.")),
                Paragraph(Text("The physical application retains the separately supplied fixed-DU "
                    + "source, memoryless outgoing-record lift, complete returned-system branches "
                    + "and identity action on untouched references. A wash has chronology J J N J J; "
                    + "its four new outgoing carriers remain unread and inaccessible. "
                    + "The original C3 preparation and control are transported through the given "
                    + "code B into C5. Universality over mathematical input matrices grants no "
                    + "additional preparations, separate D or U calls, reset, inverse, forced outcome, "
                    + "arbitrary record unitary, returned carrier, archive decoder or coherent sink access. "
                    + "The trace-norm statement with a reference is a separate result. "
                    + "No exact scalar anchor, physical precision, duration or energy bound is inferred."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula Frac(int a, int b) => new Formula.Fraction(Num(a), Num(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);

    private static Formula Statement()
    {
        var x = F.Id("X"); var n = F.Id("n"); var s = F.Id("sigma");
        var rate = Pow(Frac(2, 3), n);
        var contraction = Le(Pow(Call("HS", Call("Theta", x)), Num(2)),
            Mul(Frac(5, 12), Pow(Call("HS", x), Num(2))));
        var powers = All("n", F.Id("Nat"),
            Le(Call("HS", Call("iterateTheta", n, x)), Mul(rate, Call("HS", x))));
        var density = All("sigma", Call("PositiveSemidefiniteTraceOneMatrix", Num(3)),
            All("n", F.Id("Nat"),
                Le(Call("HS", Seq(Call("iterateTheta", n, s), Minus, Frac(1, 3), F.Id("I"))),
                    Mul(Call("sqrt", Frac(2, 3)), rate))));
        return Disp(And(All("X", Call("ComplexTraceZeroMatrix", Num(3)),
            And(contraction, powers)), density));
    }
}
