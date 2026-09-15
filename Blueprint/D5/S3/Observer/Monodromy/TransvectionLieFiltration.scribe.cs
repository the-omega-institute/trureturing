using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class TransvectionLieFiltrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Monodromy/TransvectionLieFiltration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Lie-generation filtration equals the independently constructed "
            + "pairing-graph distance bands. Nondegeneracy gives a coefficientwise "
            + "support obstruction beyond each band.",
        H("Exact Pairing-Graph Filtration of Transvection Generators"),
        Blocks(
            Paragraph(Text(
                "Let K be a field with 2 nonzero, I a finite index type with "
                    + "decidable equality, and H a skew-symmetric I-by-I matrix. "
                    + "Define N_i=e_i H(i,*) and C_ij=(E_ij+E_ji)H. All edges "
                    + "are tested by H(i,j) being nonzero.")),
            Paragraph(Text(
                "L_0 is the linear span of the actual N_i. Recursively L_(k+1) "
                    + "is L_k plus the span of the actual commutators [X,N_i] "
                    + "for X in L_k. Independently, Within(H,k,i,j) means that "
                    + "there is an actual pairing walk from i to j using at most "
                    + "k edges. B_k is the span of C_ij with this property. "
                    + "Thus L_k uses at most k+1 generator occurrences. "
                    + "No graph-distance assumption is placed into the definition "
                    + "of the Lie layer.")),
            Describe.Lean(
                DescribeId.Create("layer-eq-band"),
                DeclarationHandle.Create(Prefix + "layer_eq_band"),
                H("Every generation layer has an exact graph description"),
                StatementSource.FromAuthor(Layers()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k, L_k=B_k. Neither invertibility of H "
                        + "nor connectedness of its graph is assumed. The proof "
                        + "uses C_ii=2N_i for the base. For the forward induction, "
                        + "[C_ij,N_v]=H_jv C_iv+H_iv C_jv either extends a path "
                        + "by one actual edge or has zero coefficient. For the "
                        + "reverse induction, split a path at its last edge, "
                        + "subtract the already available edge direction, and "
                        + "divide by the nonzero last-edge coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("layer-support"),
                DeclarationHandle.Create(Prefix + "layer_support"),
                H("A shorter calculation cannot hide an out-of-band coefficient"),
                StatementSource.FromAuthor(Support()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If det(H) is nonzero and X belongs to L_k, then the (r,c) "
                        + "entry of X H-inverse is zero whenever no pairing walk "
                        + "of at most k edges joins r to c. The proof computes "
                        + "C_ij H-inverse=E_ij+E_ji from the actual inverse identity "
                        + "and extends the resulting zero-entry property through "
                        + "linear combinations. This is a lower bound from a "
                        + "genuine matrix coefficient, not a declared complexity label."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Yelton, arXiv:1703.10917v5, Remark 3.4, is prior art for "
                    + "diameter-dependent transvection-generation bounds in an "
                    + "l-adic setting. This development proves the exact full "
                    + "linear filtration together with its support obstruction. "
                    + "No claim of global priority or solution of the order-two "
                    + "Fano monodromy expectation is made.")))));

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

    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Layers() => Disp(Seq(
        Call("Skew", F.Id("H")), Sp, Land, Sp,
        Call("Nonzero", D(2)), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("k"), Comma, Sp,
        Eq(Call("layer", F.Id("H"), F.Id("k")),
            Call("band", F.Id("H"), F.Id("k")))));

    private static Formula Support() => Disp(Seq(
        Call("Skew", F.Id("H")), Sp, Land, Sp,
        Call("Nonzero", D(2)), Sp, Land, Sp,
        Call("Nonzero", Call("det", F.Id("H"))), Sp, Land, Sp,
        Call("Member", F.Id("X"), Call("layer", F.Id("H"), F.Id("k"))),
        Sp, Land, Sp, Call("NoWalkWithin", F.Id("H"), F.Id("k"), F.Id("r"), F.Id("c")),
        Sp, Rightarrow, Sp,
        Eq(Call("inverseCoefficient", F.Id("X"), F.Id("H"), F.Id("r"), F.Id("c")), D(0))));
}
