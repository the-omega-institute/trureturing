using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatStripBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Observer/Linear/ReflectingHeatStripBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-diagonal lower bound for the reflecting heat grid",
        H("Inverse-diagonal lower bound for the reflecting heat grid"),
        Blocks(
            Paragraph(Text("On n cells the physical generator takes the second difference with reflecting ghost cells and multiplies by n². Write Gₙ for this generator and Wₙ(T) for its observed Gramian. The cell mass is 1/n. The indices i range over Fin(n) and j,k over Fin(n−1). The symbol δⱼₖ is the Kronecker delta. The positive frequencies are j+1 for j in Fin(n−1). Their dimensionless rates qⱼ are 2−2 cos(π(j+1)/n), and their real cell-centered profiles are √2 cos(π(j+1)(i+1/2)/n).")),
            Claim("reflecting-generator-eigenmode", "reflectingGenerator_cellMode",
                "Physical eigenvalue with reflecting endpoints", Eigenmode(),
                "At the endpoints the ghost cells repeat the adjacent cell values. Extending the cosine through the ghosts makes the same centered second-difference identity valid at every cell. The eigenvalue is −n²qⱼ."),
            Claim("positive-mode-zero-mean", "cellMode_sum_zero", "Zero cell mean", Mean(),
                "The cosine sum from the geometric progression vanishes at each retained frequency."),
            Claim("positive-mode-mass-inner-product", "cellMode_mass_inner", "Mass orthonormality", MassInner(),
                "The product-to-sum identity reduces the mass pairing to the sum and difference frequencies. The constant contribution gives one exactly on the diagonal."),
            Claim("reflecting-modal-evolution", "reflectingHeatFlow_spec",
                "Heat evolution in mass coordinates", Evolution(),
                "For each n and each real initial coefficient family c on Fin(n−1), let u be the sum of the modes with coefficients cⱼ exp(−n²qⱼt). At every real t and every cell i, its time derivative is the reflecting generator applied to u. The zero means and mass orthonormality of the modes give the other two identities."),
            Describe.Lean(DescribeId.Create("physical-inverse-diagonal-lower-bound"),
                DeclarationHandle.Create(Owner + "inverse_diagonal_lower_bound"),
                H("Finite strip lower bound on the physical inverse diagonal"), StatementSource.FromAuthor(InverseDiagonal()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Observation at the first cell gives bⱼ = √(2−qⱼ/2), which is positive. The physical Gramian integrates products of bⱼ exp(−n²qⱼt) in Lebesgue time. Distinct rates and nonzero weights give invertibility on every positive window. Vanishing energy forces the synthesized exponential sum to vanish throughout the window. Sampling at successive equally spaced interior times then gives a Vandermonde system with distinct nodes.")),
                    Paragraph(Text("For n ≥ 2, positive a and β, and any retained j, set T=a/n and rₖ = √(qₖ²+β²). Synthesize a signal using column j of the inverse Gramian. Multiplying that signal by bⱼ gives an exact Kronecker moment function whose L² norm is bⱼ times the square root of inverse entry (j,j). Apply the finite-window theorem at decay nodes n²q and strip parameter n²β. Homogeneity cancels n² in the node ratios, and the damping uses the scaled duration na. Dividing by the observed weight and writing the norm on this scale gives the factor n/bⱼ."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Claim(string id, string declaration, string heading, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(heading), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static Formula N => F.Id("n");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula K => F.Id("k");
    private static Formula A => F.Id("a");
    private static Formula Q(Formula i) => Sub(F.Id("q"), i);
    private static Formula R(Formula i) => Sub(F.Id("r"), i);
    private static Formula Mode(Formula j) => Sub(Phi, j);
    private static Formula Sub(Formula x, Formula i) => Seq(x, Underscore, Grp(i));
    private static Formula Value(Formula j) => new Formula.Apply(Mode(j), [I]);
    private static Formula CellSum => Seq(Sum,
        Underscore, Grp(I, InMacro, Sp, new Formula.Apply(F.Id("Fin"), [N])), Sp);

    private static Formula Eigenmode() => Disp(Seq(
        new Formula.Apply(new Formula.Apply(Sub(F.Id("G"), N), [Mode(J)]), [I]), Eq,
        Minus, new Formula.Power(N, D(2)), Sp, Q(J), Sp, Value(J)));

    private static Formula Mean() => Disp(Seq(CellSum, Value(J), Eq, D(0)));

    private static Formula MassInner() => Disp(Seq(
        new Formula.Fraction(Seq(CellSum, Value(J), Value(K)), N), Eq, Sub(DeltaLower, Seq(J, K))));

    private static Formula Evolution()
    {
        Formula t = F.Id("t"), u = F.Id("u");
        Formula value = new Formula.Apply(u, [t, I]);
        Formula derivative = new Formula.Fraction(F.Id("d"), Seq(F.Id("d"), t));
        Formula state = new Formula.Apply(u, [t, Cdot]);
        Formula generator = new Formula.Apply(new Formula.Apply(Sub(F.Id("G"), N), [state]), [I]);
        Formula decay = new Formula.Apply(Exp, [Seq(Minus, new Formula.Power(N, D(2)),
            Sp, Q(J), Sp, t)]);
        return Disp(Seq(Begin, Grp(F.Id("gathered")), derivative, Sp, value, Eq, generator,
            RowBreak, CellSum, value, Eq, D(0), RowBreak,
            new Formula.Fraction(Seq(CellSum, value, Value(J)), N), Eq,
            Sub(F.Id("c"), J), Sp, decay, End, Grp(F.Id("gathered"))));
    }

    private static Formula InverseDiagonal()
    {
        Formula index = Seq(K, InMacro, Sp,
            new Formula.Apply(F.Id("Fin"), [Seq(N, Minus, D(1))]), Setminus, OpenBrace, J, CloseBrace);
        Formula product = Seq(Prod, Underscore, Grp(index), Sp,
            new Formula.Fraction(Seq(R(J), Plus, R(K)), new Formula.Absolute(Seq(Q(J), Minus, Q(K)))));
        Formula damping = new Formula.Apply(Exp, [new Formula.Fraction(
            Seq(Minus, N, Sp, A, Open, R(J), Minus, Q(J), Close), D(2))]);
        Formula matrix = new Formula.Apply(Sub(F.Id("W"), N), [new Formula.Fraction(A, N)]);
        Formula inverse = new Formula.Power(matrix, Seq(Minus, D(1)));
        return Disp(Seq(new Formula.Fraction(N, Sub(F.Id("b"), J)), Sp,
            new Formula.Fraction(Seq(product, Sp, damping), Seq(Sqrt, Grp(N, Sp, A))), Sp, Le, Sp,
            Sqrt, Grp(Sub(Seq(Open, inverse, Close), Seq(J, J)))));
    }
}
