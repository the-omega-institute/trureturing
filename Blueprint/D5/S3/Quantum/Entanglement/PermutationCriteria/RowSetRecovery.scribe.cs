using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PermutationCriteria;

internal sealed class RowSetRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula r = F.Id("r"), s = F.Id("S"), t = F.Id("T");
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula sites = Call("Fin", r), positions = Call("Fin", new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, r));
        Formula sets = Call("Finset", positions);
        Formula Label(Formula set, Formula site) => Call("rowLabels", set, site);
        Formula side = All(k, sites,
            new Formula.Logic(Call("sameSide", Label(s, k)), FormulaLogicOperator.Iff, Call("sameSide", Label(t, k))));
        Formula distances = All(i, sites, All(j, sites,
            Equal(Call("pairDistance", Label(s, i), Label(s, j)), Call("pairDistance", Label(t, i), Label(t, j)))));
        Formula image = Call("map", s, Call("J", r));
        Formula choices = Or(Equal(t, s), Or(Equal(t, Call("compl", s)),
            Or(Equal(t, image), Equal(t, Call("compl", image)))));
        Formula statement = All(r, Seq(Mathbb, Grp(F.Id("N"))), All(s, sets, All(t, sets,
            Imp(side, Imp(distances, choices)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Interleaved subsets with identical sector and pair-distance data differ by at most simultaneous ket-bra exchange and complement.",
            H("Recovering interleaved row subsets"),
            Blocks([
                .. SetupDescriptions.Items(),Describe.Lean(
                DescribeId.Create("interleaved-row-subset-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.recover_rowSets"),
                H("Four possibilities for the interleaved subset"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every factor k, rowLabels(S,k) records membership of positions 2k and 2k+1 in S. "
                    + "Equal sector and distance data give the two global Boolean operations from recover_labels. "
                    + "Every interleaved position is a ket or bra position, so its label determines membership. "
                    + "Boolean complement is set complement, and exchange of the two labels is the image under J. "
                    + "The statement applies to all subsets, including unbalanced subsets and the empty carrier; no cardinality assumption is required."))),
                DescribeRole.Theorem)]),
            [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Quantum/Entanglement/PermutationCriteria/LabelRecovery")),
]));
    }

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula x, Formula domain, Formula body) => Seq(Forall, Sp, x, Colon, domain, Comma, Sp, Par(body));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Or, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
}

internal static class SetupDescriptions
{
    private static DocumentBlock.Describe Item(string name, string title, string body,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("permutation-criteria-setup-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery." + name),
            H(title), StatementSource.WithoutFormula(), name is "permute" or "Dependent"
                ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/clarissewocjan2005permutationcriteria"))
                : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), role);

    public static DocumentBlock[] Items() => [

            Item("Index", "Tensor indices", "For natural numbers r and d, Index r d is the function type from Fin r to Fin d.", DescribeRole.Definition),
            Item("IsDensity", "Density matrices", "This is the existing predicate for a positive semidefinite complex matrix with trace one, on any finite index type.", DescribeRole.Definition),
            Item("ketPos", "Ket positions", "The ket position of a factor k in Fin r is the element 2k of Fin (2r).", DescribeRole.Definition),
            Item("braPos", "Bra positions", "The bra position of a factor k in Fin r is the element 2k+1 of Fin (2r).", DescribeRole.Definition),
            Item("party", "The factor of a position", "The factor containing a position p in Fin (2r) has index floor(p/2) in Fin r.", DescribeRole.Definition),
            Item("merge", "Interleaving row and column coordinates", "For row and column functions a and b from Fin r to Fin d, merge a b at position p is a(floor(p/2)) when p is even, and b(floor(p/2)) when p is odd.", DescribeRole.Definition),
            Item("entry", "Reading an interleaved entry", "For an operator rho on Index r d and a flat coordinate function i, entry rho i is rho evaluated at the row k mapped to i(2k) and the column k mapped to i(2k+1).", DescribeRole.Definition),
            Item("permute", "The original index permutation", "For every permutation sigma of Fin (2r), permute sigma rho at a,b is entry rho at the function p mapped to merge a b (sigma p). This is the source index-permutation convention, without an inverse permutation.", DescribeRole.Definition),
            Item("Dependent", "Dependence on every quantum state", "For natural r,d and permutations sigma,mu of Fin (2r), Dependent r d sigma mu means that for every complex operator rho on Index r d, positivity and trace one imply equality of traceNorm(permute sigma rho) and traceNorm(permute mu rho). The trace norm is real trace of the positive square root of the adjoint Gram matrix.", DescribeRole.Definition),
            Item("rowSet", "Original positions assigned to output rows", "For a permutation sigma of Fin (2r), rowSet sigma contains precisely the positions p for which sigma p is even. It is the preimage of the even output positions.", DescribeRole.Definition),
            Item("party_ketPos", "The factor of a ket slot", "For every r and every factor k in Fin r, party(ketPos k) equals k."),
            Item("party_braPos", "The factor of a bra slot", "For every r and every factor k in Fin r, party(braPos k) equals k."),
            Item("merge_ketPos", "The ket projection of interleaving", "For all natural r,d, row and column indices a,b, and factors k, merge a b (ketPos k) equals a k."),
            Item("merge_braPos", "The bra projection of interleaving", "For all natural r,d, row and column indices a,b, and factors k, merge a b (braPos k) equals b k."),
            Item("ketPos_party", "Recovering an even position", "For every r and p in Fin (2r), if p is even then ketPos(party p) equals p."),
            Item("braPos_party", "Recovering an odd position", "For every r and p in Fin (2r), if p is not even then braPos(party p) equals p."),
            Item("merge_projections", "Lossless splitting of flat coordinates", "For all natural r,d and every flat coordinate function i, interleaving its even and odd projections recovers i as a function."),
            Item("J", "Simultaneous ket and bra exchange", "For every r, J r is the permutation of Fin (2r) that exchanges 2k with 2k+1 for every factor k.", DescribeRole.Definition),
            Item("J_ketPos", "Exchange sends ket to bra", "For every r and k in Fin r, J r (ketPos k) equals braPos k."),
            Item("J_braPos", "Exchange sends bra to ket", "For every r and k in Fin r, J r (braPos k) equals ketPos k."),
            Item("merge_J", "Exchange swaps row and column indices", "For all natural r,d, tensor indices a,b and positions p, merge a b (J r p) equals merge b a p."),
            Item("permute_output_exchange", "Output exchange is matrix transpose", "For all natural r,d, permutations sigma and operators rho, permuting by J after sigma gives the ordinary transpose of permute sigma rho. No Hermitian hypothesis is required."),
            Item("mergeEquiv", "The interleaving equivalence", "For all natural r,d, mergeEquiv is the equivalence from pairs of tensor indices to flat coordinate functions, with inverse the even and odd projections.", DescribeRole.Definition),
            Item("indexPermutation", "Permutation on pairs of tensor indices", "For all natural r,d and permutations sigma, indexPermutation sigma sends a,b to the two projections of the flat function p mapped to merge a b (sigma p). It is an equivalence, including for empty index types.", DescribeRole.Definition),
            Item("permute_apply", "Reading through the index equivalence", "For every operator rho, permutation sigma, and indices a,b, permute sigma rho at a,b equals rho at the pair indexPermutation sigma (a,b)."),
            Item("permute_single", "The image of a single nonzero entry", "For all natural r,d, permutations sigma, indices a,b, and complex numbers z, permute sigma sends the matrix single a b z to the single entry of value z at the inverse image of a,b under indexPermutation sigma.")
    ];
}
