using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class C129ParaboloidSliceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive two-by-two Gram region has a nonnegative Schur residual and paraboloid coordinates.",
        H("C129 Paraboloid Slice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("c129-positive-two-by-two-blocks-have-paraboloid-coordinates"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/C129ParaboloidSlice.paraboloid_slice"),
                H("Positive two-by-two blocks and the zero-diagonal boundary"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real p and q and a complex cross term b, "
                            + "twoByTwoPositive records nonnegative diagonal entries and "
                            + "the determinant inequality for the Hermitian two-by-two block. "
                            + "When p is positive, the block is positive exactly when the "
                            + "Schur residual q - normSq(b)/p is nonnegative.")),
                    Paragraph(Text(
                        "The normalized real and imaginary cross-term coordinates are "
                            + "Re(b)/sqrt(p) and Im(b)/sqrt(p). Their squared coordinates "
                            + "together with the Schur residual recover q, so the allowed "
                            + "region is the paraboloid and its upper region. At p = 0, "
                            + "positivity forces b = 0 while q remains nonnegative."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);

    private static Formula TheoremFormula()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        var b = F.Id("b");
        var positive = Apply("twoByTwoPositive", p, q, b);
        var residual = Apply("residual", p, q, b);
        var coordinates = Equal(q, Seq(
            Apply("xCoord", p, b), Caret, Grp(D(2)), Sp, Plus, Sp,
            Apply("yCoord", p, b), Caret, Grp(D(2)), Sp, Plus, Sp, residual));
        var positiveBranch = Seq(
            D(0), Sp, Lt, Sp, p, Sp, Rightarrow, Sp,
            Parenthesized(Seq(
                Parenthesized(Seq(
                    positive, Sp, Iff, Sp,
                    Seq(D(0), Sp, Leq, Sp, residual))), Sp, Land, Sp,
                coordinates)));
        var zeroBranch = Seq(
            Equal(p, D(0)), Sp, Rightarrow, Sp,
            positive, Sp, Rightarrow, Sp,
            Parenthesized(Seq(Equal(b, D(0)), Sp, Land, Sp,
                D(0), Sp, Leq, Sp, q)));
        return Disp(Seq(
            Forall, Sp, p, Comma, Sp, q, Comma, Sp, b, Sp, Rightarrow, Sp,
            Parenthesized(Seq(
                Parenthesized(positiveBranch), Sp, Land, Sp,
                Parenthesized(zeroBranch)))));
    }
}
