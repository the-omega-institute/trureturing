using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.MultipartiteMonotones;

internal sealed class CarrozzaChevrierLionniConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/carrozzachevrierlionni2026detection");

    private static readonly LibraryNoteRef Cluster =
        LibraryNoteRef.Create("D5/L/QuantumStates/gourwallach2010fourqubits");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-qubit cluster state is irreducible in the sense of Definition 1 and has zero ordered and color-averaged readouts at every integer order at least two.",
        H("A four-qubit counterexample to both converses of Corollary 7"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("corollary-seven-converses"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The two universal converse assertions"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("claim"), Sp, Iff, Sp,
                    Paren(Converse(true)), Sp, Lor, Sp, Paren(Converse(false))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The sentence after Corollary 7 asks whether irreducibility implies strict positivity of the ordered readout or its color-symmetric version. Each disjunct universally quantifies over positive finite local dimensions, normalized complex pure states, and integer orders at least two. The ordered disjunct also universally quantifies over color permutations. In Lean, the parameter k is D minus three, d gives the local dimensions, and hd proves their positivity. H with subscript d is the tensor product of the complex spaces of dimensions d(i). Irred means the negation of ReducibleTensor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("both-converses"),
                DeclarationHandle.Create(Module + ".result"),
                H("Both universal converses fail"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source, Cluster),
                Blocks(
                    Paragraph(Text(
                        "Use the four-qubit cluster state C1 of Gour and Wallach, Eq. (3). Its amplitudes are 1/2 on 0000, 0011 and 1100, −1/2 on 1111, and zero elsewhere. The four nonzero terms give squared norm one.")),
                    new DocumentBlock.DisplayFormula(WitnessFormula()),
                    Paragraph(Text(
                        "The proof takes D = 4, all local dimensions equal to two and n = 2 in each putative universal assertion. The ordered vanishing holds for every permutation, so the same state also defeats strict positivity with an existential choice of order of the colors. The three-qubit restriction in Proposition 8 and the spectral-hypergraph-tensor restriction in Theorem 6 are separate source results."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("carrozza-chevrier-lionni-2026-corollary-seven-converses"),
                    ResolutionKind.Refuted)),
            Paragraph(Text(
                "Definition 1 and Eq. (9) correspond to ReducibleTensor in finite orthonormal bases. Each factor has a proper assigned support, with arbitrary positive finite dimensions on it and a normalized coefficient tensor. Outside its support a product unit leg can be compressed to dimension one using the isometry that sends the scalar unit to that leg. The empty support allows a unit scalar. The code uses a list of proper supports. An Eq. (9) family gives such a list by enumerating the proper subsets. Conversely, regroup factors with the same support, multiply their local dimensions and pad absent supports with unit scalar factors. Local reindexing is unitary. The two sets of matrices U and V are the local isometries into common spaces in the cited Definition 2.2 of local-unitary equivalence. Compose one set with the comparison unitary to obtain the exact equality of embedded tensors in ReducibleTensor. Conversely, that equality supplies the same local-unitary equivalence with identity comparison. This permits overlapping supports and arbitrary mixing of the regrouped factor legs within each party.")),
            Paragraph(Text(
                "For any party cut, the grouped local maps act on the coefficient matrix M by L M R transpose. Left multiplication by the adjoint of L and right multiplication by the conjugate of R recover M, so the cut rank is invariant. The cut rank of a regrouped factor product is the product of the factor cut ranks. Every singleton cut of the cluster state has rank two. For every nonempty proper cut, select the constant zero and constant one coordinates on each side. The resulting minor has diagonal entries 1/2 and −1/2 and off-diagonal entries in {0, 1/2}. Its determinant is nonzero. Primality of two assigns each party to exactly one factor with singleton rank two. Every other factor has singleton rank one at that party. Each effective support lies within its assigned proper support. Stripping rank-one legs shows that the cut at a nonempty effective support has rank one in the grouped product, contradicting the minor bound.")),
            Paragraph(Text(
                "For Eq. (24), the column is ket–dual and the row is dual–ket. The active pairs follow adjacent colors of the permutation. Within each pair, summing the spectator colors gives the corresponding two-color density matrix rho. Top and bottom labels exchange ket and bra roles between successive pairs. The terminal top label is the ket for even D and the dual for odd D, which accounts for the parity-dependent output swap in contraction. For D = 4 and order (a,b,c,d), the entry at row (j′,j) and column (i,i′) is the following sum.")),
            new DocumentBlock.DisplayFormula(ChainFormula()),
            Paragraph(Text(
                "For every one of the 24 permutations the contraction gives A = e e transpose / 16 with e = (1,0,0,1) in the endpoint basis (00,01,10,11). Its Gram matrix X = A A adjoint is e e transpose / 128, has trace t = 1/64, and satisfies X squared = t X. The real part of the complex trace agrees with the real trace of powers of this positive semidefinite matrix. Hence tr(X^n) = t^n for every positive integer n. The logarithm in Eq. (30) has the positive argument one, and every term in Eq. (31) vanishes.")))));

    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Mathrm, Grp(F.Id(name))), [.. args]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Permutations(Formula count) => new Formula.Subscript(F.Id("S"), count);
    private static Formula NaturalAtLeast(byte bound) => new Formula.Subscript(Natural, Seq(Geq, D(bound)));
    private static Formula NormSquared => new Formula.Power(new Formula.Norm(Psi), D(2));

    private static Formula Readout(bool ordered)
    {
        Formula name = ordered ? new Formula.Subscript(F.Id("R"), SigmaLower) : F.Id("R");
        return Seq(name, Caret, Grp(Paren(F.Id("n"))), Paren(Psi));
    }

    private static Formula Converse(bool ordered)
    {
        Formula count = F.Id("D");
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula parties = Seq(OpenBracket, count, CloseBracket);
        Formula stateSpace = new Formula.Subscript(Seq(Mathcal, Grp(F.Id("H"))), d);
        Formula irreducible = Call("Irred", Psi);
        Formula positivity = Seq(Readout(ordered), Sp, Gt, Sp, D(0));
        Formula conclusion = ordered
            ? Seq(Forall, Sp, SigmaLower, Sp, InMacro, Sp, Permutations(count), Comma, Sp, positivity)
            : positivity;
        return Seq(
            Forall, Sp, count, Sp, InMacro, Sp, NaturalAtLeast(3), Comma, Sp,
            Forall, Sp, d, Colon, parties, Sp, To, Sp, new Formula.Subscript(Natural, Seq(Gt, D(0))), Comma, Sp,
            Forall, Sp, Psi, Sp, InMacro, Sp, stateSpace, Comma, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, NaturalAtLeast(2), Comma, Sp,
            Paren(Seq(Equal(NormSquared, D(1)), Sp, Land, Sp, irreducible)), Sp,
            Implies, Sp, Paren(conclusion));
    }

    private static Formula WitnessFormula()
    {
        Formula n = F.Id("n");
        return Seq(Equal(NormSquared, D(1)), Sp, Land, Sp, Call("Irred", Psi), Sp, Land, Sp,
            Paren(Seq(Forall, Sp, n, Sp, InMacro, Sp, NaturalAtLeast(2), Comma, Sp,
                Paren(Seq(Forall, Sp, SigmaLower, Sp, InMacro, Sp, Permutations(D(4)), Comma, Sp,
                    Equal(Readout(true), D(0)))), Sp, Land, Sp, Equal(Readout(false), D(0)))));
    }

    private static Formula ChainFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), x = F.Id("x"), y = F.Id("y");
        Formula ip = Seq(i, Apos), jp = Seq(j, Apos), xp = Seq(x, Apos), yp = Seq(y, Apos);
        return Equal(Entry(new Formula.Subscript(F.Id("A"), SigmaLower), jp, j, i, ip),
            Seq(new Formula.Subscript(Sum, Seq(x, Comma, xp, Comma, y, Comma, yp)), Sp,
                Entry(new Formula.Subscript(Rho, F.Id("ab")), i, x, ip, xp), Sp, Cdot, Sp,
                Entry(new Formula.Subscript(Rho, F.Id("bc")), xp, yp, x, y), Sp, Cdot, Sp,
                Entry(new Formula.Subscript(Rho, F.Id("cd")), y, j, yp, jp)));
    }

    private static Formula Entry(Formula matrix, Formula r1, Formula r2, Formula c1, Formula c2) =>
        Seq(matrix, OpenBracket, Paren(Seq(r1, Comma, r2)), Comma, Paren(Seq(c1, Comma, c2)), CloseBracket);
}
