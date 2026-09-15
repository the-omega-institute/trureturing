using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class PrimitiveExteriorRecognitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Monodromy/PrimitiveExteriorRecognition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic nilpotence on the actual primitive exterior subspace forces "
            + "natural square-zero rank-one factorization, with an explicit inverse "
            + "for the primitive infinitesimal action.",
        H("Recognition from Primitive Exterior Data"),
        Blocks(
            Paragraph(Text(
                "Let J be a nonsingular skew-symmetric matrix over a field K. "
                    + "Write n=card(I). The actual primitive submodule W_J consists "
                    + "of coefficient matrices B with B-transpose=-B and trace(JB)=0. "
                    + "In characteristic different from two these coefficient "
                    + "matrices represent primitive bivectors. Assume "
                    + "X-transpose J=-JX. The source proves that A_X(B)=XB+BX-transpose "
                    + "preserves W_J and defines its actual restricted linear "
                    + "endomorphism P_X. This is not an abstract packet of an "
                    + "assumed exterior lift.")),
            Paragraph(Text(
                "The source proves that J-inverse is skew-symmetric and that "
                    + "A_X(J-inverse)=0. If n is nonzero, the explicit projection "
                    + "pi_J(B)=B-trace(JB)/n times J-inverse sends skew B into W_J. "
                    + "The identity A_X(pi_J(B))=A_X(B) is proved from the invariant "
                    + "line calculation. Trace(X)=0 is also derived from "
                    + "skew-adjointness and nondegeneracy, assuming two nonzero.")),
            Describe.Lean(
                DescribeId.Create("primitive-first-contraction"),
                DeclarationHandle.Create(Prefix + "primitive_first_contraction"),
                H("Primitive data retain an explicit inverse for the natural operator"),
                StatementSource.FromAuthor(Recovery()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every i,k, summing the (i,j) entries of "
                        + "A_X(pi_J(E_kj-E_jk)) over j gives (n-2)X_ik. "
                        + "For dimension eight the coefficient is six. The formula "
                        + "itself needs only nonsingular J, skew-adjoint X and two "
                        + "nonzero. To interpret every projected input as a genuine "
                        + "primitive bivector also use skew J and n nonzero, as "
                        + "proved by project_mem_primitive. Inverting this scalar "
                        + "does not solve for an unknown exterior structure on an "
                        + "arbitrary 27-dimensional vector space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primitive-square-zero-rank-one"),
                DeclarationHandle.Create(Prefix + "primitive_square_zero_rank_one"),
                H("Primitive quadratic nilpotence determines natural rank-one nilpotence"),
                StatementSource.FromAuthor(Recognition(false)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume J is skew and nonsingular, X-transpose J=-JX, "
                            + "and the scalars 2,n,n-2,n-4 are nonzero. If the "
                            + "actual restricted endomorphism P_X satisfies "
                            + "P_X squared=0, then X squared=0 and there exist "
                            + "vectors u,v with X_ij=u_i v_j and sum_j v_j u_j=0. "
                            + "The conclusion includes the zero operator. "
                            + "For nonzero X this explicit factorization implies "
                            + "rank exactly one, without a Jordan-form assumption.")),
                    Paragraph(Text(
                        "The proof projects each genuine bivector E_kl-E_lk "
                            + "into W_J. The killed invariant line shows that "
                            + "P_X squared=0 forces the full bivector action "
                            + "squared to kill every such unit. The preceding "
                            + "contraction module then derives X squared=0, "
                            + "all vanishing two-by-two minors, and an explicit "
                            + "nonzero-pivot factorization. This is a calculated "
                            + "transfer from the actual primitive subspace, "
                            + "not a stored assumption about its extension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dimension-eight-recognition"),
                DeclarationHandle.Create(Prefix + "dimension_eight_recognition"),
                H("The eight-dimensional specialization has no residual scalar conditions"),
                StatementSource.FromAuthor(Recognition(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In characteristic zero with I=Fin(8), all scalar "
                        + "restrictions are discharged by exact arithmetic. "
                        + "The ordinary dimension of W_J is 28-1=27: "
                        + "skew coefficient matrices have dimension 28 and "
                        + "contraction is nonzero because trace(J J-inverse)=8. "
                        + "This dimension count is explained in the theory text "
                        + "and is not a separately kernel-checked statement here."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The result removes an assumed rank-one condition for a verified "
                    + "natural lift. It does not construct that lift from geometric "
                    + "Fano monodromy, prove the proposed Prym correspondence "
                    + "nonzero, or identify the given 27-dimensional local system "
                    + "with this primitive representation. All such geometric "
                    + "comparison obligations remain separate.")))));

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

    private static Formula Recovery() => Disp(Seq(
        Call("Nonsingular", F.Id("J")), Sp, Land, Sp,
        Call("SkewAdjoint", F.Id("J"), F.Id("X")), Sp, Land, Sp,
        Call("Nonzero", F.Id("2")), Sp, Rightarrow, Sp,
        new Formula.Relation(Call("primitiveContraction", F.Id("J"), F.Id("X"),
                F.Id("i"), F.Id("k")), FormulaRelationOperator.Equal,
            Call("multiply", Subtract(F.Id("n"), F.Id("2")),
                Call("X", F.Id("i"), F.Id("k"))))));

    private static Formula Recognition(bool eight) => Disp(Seq(
        Call(eight ? "CharacteristicZeroDimensionEight" : "NonzeroScalars2nnMinus2nMinus4"),
        Sp, Land, Sp, Call("NonsingularSkew", F.Id("J")), Sp, Land, Sp,
        Call("SkewAdjoint", F.Id("J"), F.Id("X")), Sp, Land, Sp,
        Call("SquareZero", Call("primitiveAction", F.Id("J"), F.Id("X"))),
        Sp, Rightarrow, Sp, Call("SquareZero", F.Id("X")), Sp, Land, Sp,
        Call("ExistsOuterFactorWithZeroContraction", F.Id("X"))));
}
