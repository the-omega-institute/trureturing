using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class TraceSymplecticCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Monodromy/TraceSymplecticCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar trace data construct an invariant alternating form, determine every "
            + "alternating invariant form up to an explicit scalar, and expose the exact "
            + "determinant obstruction to nondegeneracy.",
        H("An Observable Symplectic Certificate"),
        Blocks(
            Paragraph(Text(
                "Work over any field K on a finite index type I with decidable equality. "
                    + "Fix a in I, pair data p with p_i nonzero for i different from a, "
                    + "and triangle data t. Let R be recoveredGram from the preceding "
                    + "module. Put mu_a=1, mu_i=-1/p_i away from a, and J=diagonal(mu)R. "
                    + "Both R and J are explicit rational functions of the observations. "
                    + "Set T_i=1+increment(R,i).")),
            Paragraph(Text(
                "The theorem reconstructed_readback computes the pair traces p_j and "
                    + "triangle traces t_ij of these actual T_i-1 on the non-anchor "
                    + "indices. Values p_a and t with an anchor index are unused coordinates. "
                    + "Zero diagonal triangle data make the increments square-zero.")),
            Describe.Lean(
                DescribeId.Create("reconstructed-generators-preserve-form"),
                DeclarationHandle.Create(Prefix + "reconstructed_generators_preserve_form"),
                H("Alternating triangles produce an invariant form"),
                StatementSource.FromAuthor(Preservation()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume t_ii=0 and t_ij=-t_ji for every i,j. The source first proves "
                        + "J_ii=0 and J_ij=-J_ji. It then expands T_i-transpose J T_i "
                        + "using actual matrix multiplication. The linear terms cancel "
                        + "by the skew relation and the quadratic term vanishes because "
                        + "J_ii=0. No division by two is used, so the statement includes "
                        + "characteristic two. A nondegenerate J is separately required "
                        + "to interpret this as a symplectic representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariant-alternating-form-unique"),
                DeclarationHandle.Create(Prefix + "invariant_alternating_form_unique"),
                H("The observations determine all invariant alternating forms"),
                StatementSource.FromAuthor(Uniqueness()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose b different from a. For any matrix B with B_ii=0 and "
                        + "B_ij=-B_ji that satisfies T_i-transpose B T_i=B for every i, "
                        + "one has B=B(a,b)J. This theorem does not assume that the "
                        + "triangle data are alternating, or that the representation "
                        + "is irreducible or nondegenerate. The anchor invariance first "
                        + "makes all non-anchor entries of row a equal. Invariance under "
                        + "each remaining generator then solves every entry of B by "
                        + "division by the corresponding nonzero p_i."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("form-nondegenerate-iff"),
                DeclarationHandle.Create(Prefix + "form_nondegenerate_iff"),
                H("The recovered matrix supplies the complete rank test"),
                StatementSource.FromAuthor(Nondegeneracy()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under only the nonzero pair-data condition, det(J) is nonzero "
                        + "exactly when det(R) is nonzero. The proof factors J into "
                        + "diagonal(mu) times R and proves that every mu_i is nonzero. "
                        + "Thus an eight-dimensional coordinate packet with a radical "
                        + "cannot be silently interpreted as a nondegenerate Sp8 representation."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Eberhard, arXiv:2308.07086v3, Proposition 3.4 is prior art for detecting "
                    + "invariant forms by cycle reversal. The rational star formulas "
                    + "here are a concrete specialization with explicit uniqueness "
                    + "and rank bookkeeping. They do not establish the geometric "
                    + "order-two expectation in arXiv:2604.20970.")))));

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

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Preservation() => Disp(Seq(
        Call("NonzeroPairs", F.Id("p"), F.Id("a")), Sp, Land, Sp,
        Call("Alternating", F.Id("t")), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("i"), Comma, Sp,
        Eq(Call("congruence", Call("T", F.Id("i")), F.Id("J")), F.Id("J"))));

    private static Formula Uniqueness() => Disp(Seq(
        Call("NonzeroPairs", F.Id("p"), F.Id("a")), Sp, Land, Sp,
        Call("Distinct", F.Id("b"), F.Id("a")), Sp, Land, Sp,
        Call("AlternatingInvariant", F.Id("B"), F.Id("T")), Sp, Rightarrow, Sp,
        Eq(F.Id("B"), Call("smul", Call("B", F.Id("a"), F.Id("b")), F.Id("J")))));

    private static Formula Nondegeneracy() => Disp(Seq(
        Call("NonzeroPairs", F.Id("p"), F.Id("a")), Sp, Rightarrow, Sp,
        Eq(Call("Nonzero", Call("det", F.Id("J"))),
            Call("Nonzero", Call("det", F.Id("R"))))));
}
