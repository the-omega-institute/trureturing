using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CrossingMatrixDeterminantDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Recurrence/CrossingMatrixDeterminant.crossing_det_pow_sub_one";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive powers of two crossing matrices have a strict determinant obstruction.",
        H("Crossing-Matrix Determinant Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("crossing-matrix-determinant-obstruction"),
            DeclarationHandle.Create(Declaration),
            H("Both crossing-matrix power shifts are nonsingular"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For positive natural numbers k and n, let "
                        + "C_k=!![4k+1,1;4k,1] and "
                        + "D_k=!![2k+1,2;2k(k+1),2k+1]. Both integer matrices have "
                        + "determinant one and trace 4k+2.")),
                Paragraph(Text(
                    "A real Vieta pair for an arbitrary two by two integer matrix with "
                        + "this determinant and trace, together with the frozen "
                        + "trace_pow_eq_add_pow theorem, expresses the trace of its nth "
                        + "power as a^n+b^n. The strict positivity of (a^n-1)^2 for "
                        + "k>0 and n>0 gives trace greater than two.")),
                Paragraph(Text(
                    "For a determinant-one matrix M of size two, expansion gives "
                        + "det(M-I)=2-tr(M). Applying the strict trace bound to C_k "
                        + "makes this determinant negative and therefore nonzero. The same "
                        + "argument applied to D_k makes det(D_k^n-I) nonzero.")),
                Paragraph(Text(
                    "This result does not establish the Smith-form cardinality "
                        + "#(Z^2/MZ^2)=|det(M)|, nor the cardinalities of the return groups "
                        + "R(C_k,n) and R(D_k,n)."))),
            DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Observation/MatrixTracePowerSum"))]));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula MatrixName(string name, Formula index) =>
        Seq(F.Id(name), Underscore, Grp(index));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula ShiftedPower(Formula matrix, Formula exponent) =>
        Seq(Power(matrix, exponent), Sp, Minus, Sp, F.Id("I"));

    private static Formula Call(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula c = MatrixName("C", k);
        Formula d = MatrixName("D", k);
        Formula cShift = ShiftedPower(c, n);
        Formula dShift = ShiftedPower(d, n);
        Formula cDet = Call("det", cShift);
        Formula dDet = Call("det", dShift);
        Formula cTrace = Call("tr", Power(c, n));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, k, Comma, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                Num(0), Sp, Lt, Sp, k, Sp, Land, Sp, Num(0), Sp, Lt, Sp, n,
                Sp, Rightarrow),
            Seq(
                Left, Open, cDet, Sp, Eq, Sp, Num(2), Sp, Minus, Sp, cTrace,
                Right, Close, Sp, Land),
            Seq(
                Left, Open, cDet, Sp, Lt, Sp, Num(0), Right, Close, Sp, Land),
            Seq(
                Left, Open, cDet, Sp, Neq, Sp, Num(0), Right, Close, Sp, Land),
            Seq(
                Left, Open, dDet, Sp, Neq, Sp, Num(0), Right, Close, Dot),
        ]));
    }
}
