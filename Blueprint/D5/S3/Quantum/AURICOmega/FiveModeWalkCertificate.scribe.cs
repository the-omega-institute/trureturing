using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class FiveModeWalkCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The analytic five-mode walk has full support at wait two thirds.",
        H("The five-mode walk at two thirds"),
        Blocks(Describe.Lean(DescribeId.Create("auric-omega-actual-five-mode-walk"),
            DeclarationHandle.Create("D5/S3/Quantum/AURICOmega/FiveModeWalkCertificate.actual_walk_certificate"),
            H("Orthogonality and five strict coordinate bounds"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The mode order is (N,2,3,5,25), with N indexed by 0. The real generator is A=[[0,1,1,1,0],[-1,0,0,0,-1],[-1,0,0,0,0],[-1,0,0,0,-1],[0,1,0,1,0]]. Put X=(2/3)A, O=exp(X), and S=sum from k=0 to 12 of X^k/k!. The transpose relation A^T=-A and Mathlib's matrix exponential product theorem give both orthogonality identities.")),
                Paragraph(Text("The matrix norm throughout the remainder estimate is the induced maximum row-sum norm. Its bound for X is 2. The general exponential remainder theorem gives norm(O-S) at most (7/6) times 2^13/13!, equal to 4/2606175. The successive scalar majorant ratios are at most 1/7. This is smaller than 64/6081075.")),
                Paragraph(Text("The first row of S is exactly [107738440637/248594813775,490347766/1104865839,4899328858/9207215325,490347766/1104865839,-91371050044/248594813775]. Its absolute entries all exceed 367/1000. Subtracting the proved analytic remainder gives absolute entries of the actual O strictly greater than 9/25. Their squares exceed 1/8 and sum to one. The notation squareSum(v) denotes the sum of the five squared coordinates, and minimumSquaredCoordinate(v) denotes their finite minimum.")),
                Paragraph(Text("The vector v=O^T e_N has these five entries, so it is a unit vector with full support. Since Fin 5 is nonempty and finite, its minimum squared coordinate exceeds 1/8. The real coordinate calculation is used within the full complex Hilbert space; it imposes no restriction to real input density matrices. The diagonal frame D=diag(1,i,i,i,1) is a passive change of coordinates. The wait 2/3 is a nonnegative mathematical parameter and supplies no physical calibration or additional operation.")),
                Paragraph(Text("Connected-probe rigidity is the standard result of Mayer and Knill, Quantum Process Fidelity Bounds from Sets of Input States, arXiv:1805.04491v1, Theorem 1. Measurement-relative compression uses the common encoder and decoder model of Bluhm, Rauber and Wolf, arXiv:1708.04898v4. Koashi and Imoto, quant-ph/0101144, provide broader no-disturbance structure. The present statement supplies the analytic probe bounds; channel rigidity and compression bounds require their own channel and port hypotheses."))),
            DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] x) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. x]);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Rat(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Statement()
    {
        Formula o = Call("actualFiveModeExponential", Rat(D(2), D(3)));
        Formula s = Call("actualFiveModeTaylor", Rat(D(2), D(3)), D(1,3));
        Formula v = Call("mulVec", Call("transpose", o), Call("basisVector", D(5), D(0)));
        Formula j = F.Id("j"), entry = Call("coordinate", v, j);
        Formula all(Formula p) => new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("j"), Call("Fin", D(5)), p);
        Formula tail = Rat(Mul(Rat(D(7), D(6)), new Formula.Power(D(2), D(1,3))), Call("factorial", D(1,3)));
        return Disp(And(Eq(Mul(Call("transpose", o), o), D(1)),
            And(Eq(Mul(o, Call("transpose", o)), D(1)),
            And(Le(new Formula.Norm(new Formula.Binary(o, FormulaBinaryOperator.Subtract, s)), tail),
            And(all(Lt(Rat(D(9), D(2,5)), new Formula.Absolute(entry))),
            And(all(Lt(Rat(D(1), D(8)), new Formula.Power(entry, D(2)))),
                And(Lt(Rat(D(1), D(8)), Call("minimumSquaredCoordinate", v)),
                Eq(Call("squareSum", v), D(1)))))))));
    }
}
