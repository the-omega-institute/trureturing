using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class ToralReturnModuleSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Dynamics/ToralReturnModuleSpectrum.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An infinite family has equal sizes of all actual integer return quotients, "
        + "while every integral intertwiner has even determinant.",
        H("Return module spectra and integral conjugacy"),
        Blocks(
            Paragraph(Text("For k in N, C_k=[[4k+1,1],[4k,1]] and "
                + "D_k=[[2k+1,2],[2k(k+1),2k+1]]. Both have determinant one. "
                + "R(A,n) is the actual quotient Z^2/(A^n-I)Z^2, with column-vector convention.")),
            Describe.Lean(DescribeId.Create("same-return-determinant"),
                DeclarationHandle.Create(Prefix + "same_return_determinant"),
                H("All-time signed determinant equality"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k,n"), Colon, Sp, Natural(), Comma, Sp,
                    Call("det", ReturnMatrix("C", "n")), Sp, Eq, Sp,
                    Call("det", ReturnMatrix("D", "n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit matrix P_k=[[1,0],[-2k,2]] satisfies "
                    + "C_k P_k=P_k D_k and det(P_k)=2. Induction intertwines every power. "
                    + "Taking determinants of (C_k^n-I)P_k=P_k(D_k^n-I) and cancelling "
                    + "the nonzero integer two proves the equality, including n=0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equal-return-module-cardinality"),
                DeclarationHandle.Create(Prefix + "equal_cardinality_return_modules"),
                H("The actual quotients have equal positive cardinalities"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k,n"), Colon, Sp, Natural(), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("k"), Sp, Land, Sp,
                    D(0), Sp, Lt, Sp, F.Id("n"), Sp, Rightarrow, Sp,
                    Card("C"), Sp, Eq, Sp, Card("D"), Sp, Land, Sp,
                    D(0), Sp, Lt, Sp, Card("C")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative matrix powers have diagonal entries at least one; "
                    + "positive k and n give trace(C_k^n)>2. Since the determinant of each power is one, "
                    + "its return matrix has negative determinant. The map from Z^2 onto its image "
                    + "is therefore injective. Mathlib's integer-lattice determinant/index theorem "
                    + "then computes Nat.card of the genuine quotient. The zero-time infinite "
                    + "quotient is excluded from this finite-cardinality statement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-intertwiner-determinant"),
                DeclarationHandle.Create(Prefix + "intertwiner_determinant_even"),
                H("A uniform prime-two obstruction"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Colon, Sp, Natural(), Comma, Sp,
                    Forall, Sp, F.Id("P"), Colon, Sp, Call("Matrix2", Integer()), Comma, Sp,
                    Seq(F.Id("C"), F.Id("P")), Sp, Eq, Sp, Seq(F.Id("P"), F.Id("D")),
                    Sp, Rightarrow, Sp, Call("Divides", D(2), Call("det", F.Id("P")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two top-row equations force P_10=2k((k+1)P_01-P_00) "
                    + "and P_11=2(P_00-kP_01). The bottom row is even, hence the determinant "
                    + "is even. No unimodular integral intertwiner can exist."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("return-spectrum-integral-boundary"),
                DeclarationHandle.Create(Prefix + "spectrum_does_not_determine_integral_conjugacy"),
                H("Complete scalar return data does not determine integral conjugacy"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Colon, Sp, Natural(), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("k"), Sp, Rightarrow, Sp,
                    Open, Forall, Sp, F.Id("n"), Colon, Sp, Natural(), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("n"), Sp, Rightarrow, Sp,
                    Card("C"), Sp, Eq, Sp, Card("D"), Sp, Land, Sp,
                    D(0), Sp, Lt, Sp, Card("C"), Close, Sp, Land, Sp,
                    Call("NoIntegralUnimodularIntertwiner", F.Id("C"), F.Id("D"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The final statement combines the all-positive-time quotient "
                    + "calculation with exclusion of every determinant-plus-or-minus-one intertwiner. "
                    + "NoIntegralUnimodularIntertwiner abbreviates that exact nonexistence statement. "
                    + "This module does not construct a topological mapping torus, identify singular "
                    + "homology, or prove a new profinite-rigidity result. Classical context is "
                    + "Rodrigues--Ramos (arXiv:math/0303185) and Bakker--Rodrigues (arXiv:2207.00922)."))),
                DescribeRole.Theorem))));

    private static Formula Natural() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integer() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ReturnMatrix(string matrix, string time) =>
        Seq(F.Id(matrix), Caret, Grp(F.Id(time)), Sp, Minus, Sp, F.Id("I"));
    private static Formula Card(string matrix) => Call("Nat.card", Call("R", F.Id(matrix), F.Id("n")));
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
