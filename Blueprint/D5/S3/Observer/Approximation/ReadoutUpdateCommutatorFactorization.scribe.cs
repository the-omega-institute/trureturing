using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Approximation;

internal sealed class ReadoutUpdateCommutatorFactorizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization."
            + "readout_update_commutator_factorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The readout-update commutator factors on its common domain and has the exact defect norm when bounded.",
        H("Readout-Update Commutator Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("readout-update-commutator-factorization"),
                DeclarationHandle.Create(Declaration),
                H("The commutator factors and has the defect norm"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let I be an address type, tau a reversible address permutation, and "
                            + "f a complex readout coefficient. The first conjunct identifies the "
                            + "independently constructed commutator with multiplication by the "
                            + "update defect after the update, on their natural common domain.")),
                    Paragraph(Text(
                        "For every proof that I is finite or f belongs to lp infinity, the second "
                            + "conjunct states that the norm of the bounded commutator is exactly "
                            + "the lp-infinity norm of the bundled update defect."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "A consequence of the shift and multiplication operators is lower-norm "
                    + "localization for scalar complex tridiagonal operators. Let H be "
                    + "l2(Z; C), let e_j have coordinate one at j and zero elsewhere, and let "
                    + "A be an arbitrary bounded complex-linear operator on H. Assume only "
                    + "that (A e_j)_i is zero unless i is j-1, j, or j+1. Define its actual "
                    + "coefficient sequences by a_i = (A e_(i-1))_i, b_i = (A e_i)_i, and "
                    + "c_i = (A e_(i+1))_i. Each coordinate has modulus at most the operator "
                    + "norm of A, because e_j has norm one. Write Mminus for the supremum "
                    + "of the moduli of a_i and Mplus for the supremum of the moduli of c_i.")),
            Paragraph(Math(Disp(TridiagonalFormula()))),
            Paragraph(Text(
                "Here the coefficient suprema are the lp-infinity norms of the bundled "
                    + "sequences. The identity follows first on each coordinate single from "
                    + "the matrix sparsity assumption, and then on all of H by "
                    + "lp.ext_continuousLinearMap. The operators diagonalOperator and "
                    + "updateLinearIsometryEquiv supply bounded coordinate multiplication "
                    + "and the bilateral shift U, where (U x)_i = x_(i-1). Their norm and "
                    + "isometry identities identify A with M_a U + M_b + M_c U inverse. "
                    + "Thus the coefficient representation is derived from the original A.")),
            Paragraph(Text(
                "For every natural number n at least one and integer k, let E_(n,k) be the "
                    + "subspace of vectors whose coordinates vanish outside the integers "
                    + "k+1 through k+n. The restriction of A has domain E_(n,k) and codomain "
                    + "the full space H. In particular its image includes the possible "
                    + "outgoing coordinates k and k+n+1. For any such bounded map B, its "
                    + "lower norm nu(B) is the infimum of the norms of Bx over unit vectors "
                    + "in its domain. The unit spheres here are nonempty: e_(k+1) belongs "
                    + "to E_(n,k).")),
            Paragraph(Text(
                "Put theta = pi/(n+1), set w_j = sin(j theta) for j from one through n, "
                    + "and set w_j = zero at every other integer. This gives a nonzero "
                    + "vector w in H. Let S be its squared norm and T the squared norm of "
                    + "U w - w. The endpoint terms are included in T, including both of "
                    + "them when n is one.")),
            Paragraph(Math(Disp(TaperEnergyFormula()))),
            Paragraph(Text("The coordinate recurrence in "),
                Ref("D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_eigenvector"),
                Text(
                    " gives the energy identity: multiply the recurrence by the central "
                        + "sine coordinate and sum. Equivalently, take the inner product "
                        + "of w with U w + U inverse w and expand the squared difference. "
                        + "The zero coordinates outside the interval remove the exterior "
                        + "recurrence terms. Since S is positive and sin(theta/2) is "
                        + "nonnegative, the identity yields the exact ratio of norms. "
                        + "It requires neither a closed expression for S nor a computation "
                        + "of the complete finite-path spectrum.")),
            Paragraph(Text(
                "For x in H, define (D_k x)_i = w_(i-k) x_i. Each D_k x belongs to "
                    + "E_(n,k). The family F_x = (D_k x)_k belongs to l2(Z; H). Indeed, "
                    + "the nonnegative double series of squared coordinate moduli has "
                    + "column sum S times the squared modulus of x_i. Summability and "
                    + "reindexing therefore give the exact mass identity below, for "
                    + "arbitrary x of infinite support as well.")),
            Paragraph(Math(Disp(WindowMassFormula()))),
            Paragraph(Text(
                "In the family of commutators A D_k x - D_k A x, the diagonal b_i "
                    + "cancels. The other two terms have coordinates "
                    + "a_i (w_(i-k-1) - w_(i-k)) x_(i-1) and "
                    + "c_i (w_(i-k+1) - w_(i-k)) x_(i+1). Multiplication has norm "
                    + "Mminus or Mplus, both shifts preserve norms, and the two translated "
                    + "differences of w have the same norm. Apply the triangle inequality "
                    + "in l2(Z; H) to obtain the image estimate. All output coordinates "
                    + "remain in this estimate.")),
            Paragraph(Math(Disp(WindowImageFormula()))),
            Paragraph(Text(
                "Write delta_n for the error displayed below. Given any positive "
                    + "epsilon, choose a unit x with norm(Ax) less than nu(A) + epsilon/2. "
                    + "Set q = norm(Ax) + delta_n + epsilon/2. If every integer window "
                    + "satisfied norm(A D_k x) at least q times norm(D_k x), monotonicity "
                    + "of the l2 norm would give an image-family norm at least q times "
                    + "the square root of S. The image estimate instead bounds it by "
                    + "(q - epsilon/2) times the square root of S. Positivity of S and "
                    + "epsilon gives a contradiction. Consequently an actual integer k "
                    + "satisfies a strict inequality, and D_k x is nonzero. Normalize it "
                    + "to u by multiplying by the reciprocal of its norm. This supplies "
                    + "the unit vector and the strict bound for every positive epsilon. "
                    + "Taking infima gives the other conclusion.")),
            Paragraph(Math(Disp(LocalizationFormula()))),
            Paragraph(Math(Disp(ActualWindowFormula()))),
            Paragraph(Text(
                "These conclusions apply to complex nonselfadjoint operators, to n "
                    + "equal to one, and to zero operators or zero off-diagonal sequences. "
                    + "They use approximate lower-norm vectors and positive epsilon; "
                    + "attainment of either infimum is unnecessary. This is the scalar "
                    + "complex Hilbert-space application of Chandler-Wilde, Chonchaiya "
                    + "and Lindner, On spectral inclusion sets and computing spectra and "
                    + "pseudospectra, Proposition 5.1 and Corollary 5.2, pages 765-766, "
                    + "with the sine choice on page 767, DOI 10.4171/JST/514. The "
                    + "conclusions stated here concern lower norms of input restrictions; "
                    + "spectral inclusion, optimality, and physical-gap assertions require "
                    + "their respective additional statements.")))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Square(Formula value) => Seq(Grp(value), Caret, Grp(D(2)));

    private static Formula Apply(Formula value, Formula argument) => Seq(value, Open, argument, Close);

    private static Formula IntegerType() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula LowerNorm(Formula value) => Seq(Nu, Sp, Open, value, Close);

    private static Formula Mminus() => Subscript(F.Id("M"), Minus);

    private static Formula Mplus() => Subscript(F.Id("M"), Plus);

    private static Formula IntervalSpace() => Subscript(F.Id("E"), Seq(F.Id("n"), Comma, F.Id("k")));

    private static Formula RestrictedA() => Seq(F.Id("A"), Bar, Underscore, Grp(IntervalSpace()));

    private static Formula Error() => Subscript(DeltaLower, F.Id("n"));

    private static Formula TridiagonalFormula()
    {
        Formula i = F.Id("i");
        Formula x = F.Id("x");
        return Seq(
            Subscript(Apply(F.Id("A"), x), i), Sp, Eq, Sp,
            Subscript(F.Id("a"), i), Sp, Subscript(x, Subtract(i, D(1))), Plus,
            Subscript(F.Id("b"), i), Sp, Subscript(x, i), Plus,
            Subscript(F.Id("c"), i), Sp, Subscript(x, Add(i, D(1))), Comma, Sp,
            i, Sp, InMacro, Sp, IntegerType());
    }

    private static Formula TaperEnergyFormula()
    {
        Formula j = F.Id("j");
        Formula n = F.Id("n");
        Formula w = F.Id("w");
        Formula s = F.Id("S");
        Formula t = F.Id("T");
        Formula halfAngle = Seq(Frac, Grp(Theta), Grp(D(2)));
        return Seq(
            s, Sp, Eq, Sp, Sum, Underscore, Grp(Seq(j, Eq, D(1))), Caret, Grp(n), Sp,
            Square(Subscript(w, j)), Sp, Gt, Sp, D(0), Comma,
            RowBreak, Grp(),
            t, Sp, Eq, Sp, Sum, Underscore, Grp(Seq(j, Eq, D(0))), Caret, Grp(n), Sp,
            Square(Subtract(Subscript(w, Add(j, D(1))), Subscript(w, j))),
            RowBreak, Grp(),
            t, Sp, Eq, Sp, D(2), Open, D(1), Minus, Call("cos", Theta), Close, s,
            Sp, Eq, Sp, D(4), Square(Call("sin", halfAngle)), s, Comma,
            RowBreak, Grp(),
            NormOf(Subtract(Apply(F.Id("U"), w), w)), Sp, Eq, Sp,
            D(2), Call("sin", halfAngle), NormOf(w));
    }

    private static Formula WindowMassFormula()
    {
        Formula k = F.Id("k");
        Formula x = F.Id("x");
        Formula window = Apply(Subscript(F.Id("D"), k), x);
        return Seq(
            Sum, Underscore, Grp(Seq(k, Sp, InMacro, Sp, IntegerType())), Sp,
            Square(NormOf(window)), Sp, Eq, Sp, F.Id("S"), Square(NormOf(x)));
    }

    private static Formula WindowImageFormula()
    {
        Formula k = F.Id("k");
        Formula x = F.Id("x");
        Formula window = Apply(Subscript(F.Id("D"), k), x);
        Formula family = Seq(Open, Apply(F.Id("A"), window), Close, Underscore, Grp(k));
        return Seq(
            NormOf(family), Sp, Leq, Sp,
            Sqrt, Grp(F.Id("S")), NormOf(Apply(F.Id("A"), x)), Plus,
            Open, Mminus(), Plus, Mplus(), Close, Sqrt, Grp(F.Id("T")), NormOf(x));
    }

    private static Formula LocalizationFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula angle = Seq(Frac, Grp(Pi), Grp(Seq(D(2), Open, n, Plus, D(1), Close)));
        return Seq(
            Error(), Sp, Eq, Sp, D(2), Open, Mminus(), Plus, Mplus(), Close,
            Call("sin", angle), Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("inf")), Underscore,
            Grp(Seq(k, Sp, InMacro, Sp, IntegerType())), Sp,
            LowerNorm(RestrictedA()), Sp, Leq, Sp, LowerNorm(F.Id("A")), Plus, Error());
    }

    private static Formula ActualWindowFormula()
    {
        Formula k = F.Id("k");
        Formula u = F.Id("u");
        return Seq(
            Forall, Sp, Varepsilon, Sp, Gt, Sp, D(0), Comma, Sp,
            Exists, Sp, k, Sp, InMacro, Sp, IntegerType(), Comma, Sp,
            u, Sp, InMacro, Sp, IntervalSpace(), Comma,
            RowBreak, Grp(),
            NormOf(u), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            NormOf(Apply(F.Id("A"), u)), Sp, Lt, Sp,
            LowerNorm(F.Id("A")), Plus, Error(), Plus, Varepsilon);
    }

    private static Formula FactorizationFormula()
    {
        Formula index = F.Id("I");
        Formula tau = F.Id("tau");
        Formula coefficient = F.Id("f");
        Formula boundedness = F.Id("h");

        Formula exactFactorization = Equal(
            Call("readoutUpdateCommutator", tau, coefficient),
            Call("factoredReadoutUpdateCommutator", tau, coefficient));
        Formula boundedPremise = Seq(
            Call("Finite", index), Sp, Lor, Sp,
            Call("MemLp", coefficient, Infty));
        Formula exactNorm = Equal(
            NormOf(Call("boundedReadoutUpdateCommutator", tau, coefficient, boundedness)),
            NormOf(Call("boundedReadoutDefect", tau, coefficient, boundedness)));

        return Disp(Seq(
            Forall, Sp, index, Sp, Colon, Sp, F.Id("Type"), Comma, Sp,
            tau, Sp, Colon, Sp, Call("Perm", index), Comma, Sp,
            coefficient, Sp, Colon, Sp,
            index, Sp, To, Sp, Mathbb, Grp(F.Id("C")), Comma,
            RowBreak, Grp(),
            exactFactorization, Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, boundedness, Sp, Colon, Sp, boundedPremise, Comma, Sp,
            exactNorm));
    }

    private static Formula NormOf(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
