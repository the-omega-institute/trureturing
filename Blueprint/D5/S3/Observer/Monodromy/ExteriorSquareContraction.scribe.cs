using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class ExteriorSquareContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Monodromy/ExteriorSquareContraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial contraction of the genuine second additive compound recovers its "
            + "natural operator and forces rank-one nilpotence from a quadratic identity.",
        H("Partial Contraction and Quadratic Recognition"),
        Blocks(
            Paragraph(Text(
                "Over a field K and a finite index type I, write n=card(I), "
                    + "F_kl=E_kl-E_lk and A_X(B)=XB+BX-transpose. These are actual "
                    + "matrix units and an actual linear map on coefficient matrices. "
                    + "Skew coefficient matrices realize bivectors. No claimed lift "
                    + "or exterior-action table is stored as an input field.")),
            Describe.Lean(
                DescribeId.Create("first-contraction"),
                DeclarationHandle.Create(Prefix + "first_contraction"),
                H("Natural matrix entries are recovered from bivector action"),
                StatementSource.FromAuthor(Equation("firstContraction", "firstContractionFormula")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every i,k, sum_j A_X(F_kj)(i,j) equals "
                        + "(n-2)X_ik plus delta_ik trace(X). In particular, on "
                        + "trace-zero operators with n-2 nonzero this is an explicit "
                        + "left inverse, with no matrix-factorization search."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-contraction"),
                DeclarationHandle.Create(Prefix + "second_contraction"),
                H("The contracted square detects the natural square"),
                StatementSource.FromAuthor(Equation("secondContraction", "secondContractionFormula")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every i,k, sum_j A_X(A_X(F_kj))(i,j) equals "
                        + "(n-4)(X squared)_ik + 2 trace(X)X_ik "
                        + "+ delta_ik trace(X squared). The proof expands genuine "
                        + "matrix products before summing the repeated index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exterior-square-zero-rank-one"),
                DeclarationHandle.Create(Prefix + "exterior_square_zero_rank_one"),
                H("Quadratic exterior nilpotence forces a natural rank-one factorization"),
                StatementSource.FromAuthor(Recognition()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume trace(X)=0, 2, n-2 and n-4 are nonzero in K, "
                            + "and A_X squared kills every F_kl. Then X squared "
                            + "is zero and there exist vectors u,v with X_ij=u_i v_j "
                            + "and sum_j v_j u_j=0. This includes X=0. A nonzero "
                            + "X therefore has rank exactly one as an ordinary "
                            + "linear-algebra consequence of the displayed factorization.")),
                    Paragraph(Text(
                        "The diagonal sum of the second contraction first gives "
                            + "2(n-2)trace(X squared)=0. The full contraction then "
                            + "gives (n-4)X squared=0. The unsummed action-square "
                            + "formula now kills every two-by-two minor. At any "
                            + "nonzero pivot X_pq, the source constructs "
                            + "u_i=X_iq and v_j=X_pj/X_pq and proves the required "
                            + "zero scalar contraction. Nilpotence and rank one "
                            + "are conclusions, never hypotheses.")),
                    Paragraph(Text(
                        "The n-4 restriction belongs to this contraction proof; "
                            + "no claim of a counterexample in dimension four is made. "
                            + "The companion primitive-space module transfers the "
                            + "input from the actual primitive exterior-square kernel. "
                            + "No geometric Fano lift is constructed here."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Prior art includes Ofir and Margaliot, arXiv:2401.02100, for "
                    + "compound/Kronecker formulas, and Dey, Ofir and Grussler, "
                    + "arXiv:2605.27682, for multiplicative compound inversion. "
                    + "The additive construction and the primitive recognition "
                    + "application are kept distinct from that multiplicative problem.")))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Equation(string left, string right) => Disp(
        new Formula.Relation(Call(left, F.Id("X"), F.Id("i"), F.Id("k")),
            FormulaRelationOperator.Equal, Call(right, F.Id("X"), F.Id("i"), F.Id("k"))));

    private static Formula Recognition() => Disp(Seq(
        Call("TraceZero", F.Id("X")), Sp, Land, Sp,
        Call("Nonzero", F.Id("2")), Sp, Land, Sp,
        Call("Nonzero", Subtract(F.Id("n"), F.Id("2"))), Sp, Land, Sp,
        Call("Nonzero", Subtract(F.Id("n"), F.Id("4"))), Sp, Land, Sp,
        Call("ExteriorSquareQuadratic", F.Id("X")), Sp, Rightarrow, Sp,
        Call("SquareZero", F.Id("X")), Sp, Land, Sp,
        Call("ExistsOuterFactorWithZeroContraction", F.Id("X"))));
}
