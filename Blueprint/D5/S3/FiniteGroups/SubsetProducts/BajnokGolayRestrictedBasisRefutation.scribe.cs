using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts;

internal sealed class BajnokGolayRestrictedBasisRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnok2022walkadditivecombinatorics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Golay quotient has a perfect restricted three-basis of size twenty-three and lies outside Bajnok's proposed families.",
        H("A Golay quotient refutes the restricted-basis classification"),
        Blocks(
            Paragraph(Text("A perfect restricted s-basis represents every group element uniquely "
                + "as the sum of at most s distinct elements of the basis, with the empty subset "
                + "representing zero. Here the group is the quotient of binary words of length "
                + "twenty-three by the punctured binary Golay code.")),
            Entry("golay-short-word", "ShortWord", "Binary words of length twenty-three", DescribeRole.Definition,
                "ShortWord is Fin 23 -> F2, where F2 is ZMod 2."),
            Entry("golay-punctured-encoder", "puncturedEncode", "Deleting the parity coordinate", DescribeRole.Definition,
                "puncturedEncode is the F2-linear map from GolayEncoder.Message to ShortWord "
                + "obtained by composing the existing twenty-four-coordinate GolayEncoder.encode "
                + "with restriction along Fin.castSucc : Fin 23 -> Fin 24. Thus the final parity "
                + "coordinate is deleted, and the original twelve-dimensional message space is retained."),
            Entry("golay-punctured-code", "puncturedCode", "The actual punctured Golay code", DescribeRole.Definition,
                "puncturedCode is the submodule equal to the range of puncturedEncode. "
                + "The original parity-extension identity makes this encoder injective. Its "
                + "code therefore has 4096 elements. Deleting one coordinate lowers weight by "
                + "at most one, so the original minimum weight eight gives minimum weight at least seven."),
            Entry("golay-quotient-group", "GolayGroup", "The additive quotient group", DescribeRole.Definition,
                "GolayGroup is the submodule quotient ShortWord / puncturedCode, with its "
                + "induced finite abelian additive group structure."),
            Entry("golay-quotient-order", "golay_group_card", "The quotient has order 2048", DescribeRole.Theorem,
                "Nat.card GolayGroup = 2048. The ambient group has 2^23 elements, and the code "
                + "has 2^12 elements; the quotient cardinality formula gives 2^11."),
            Entry("golay-restricted-three-basis", "golay_perfect_restricted_basis", "All sums of at most three elements", DescribeRole.Theorem,
                "There exists A : Finset GolayGroup with A.card = 23 and IsPerfectRestrictedBasis 3 A. "
                + "The basis consists of the twenty-three coordinate-vector classes. The general "
                + "minimum-distance argument applies because six is less than every nonzero codeword "
                + "weight, and 1 + 23 + choose(23,2) + choose(23,3) = 2048."),
            Entry("bajnok-listed-families", "ListedFamily", "The proposed group families", DescribeRole.Definition,
                "For G : Type with AddCommGroup G, naturals s,m, and R : Type with AddCommGroup R, "
                + "ListedFamily G s m R is the disjunction: Nat.card G = 2^m; or a nonempty type "
                + "of additive equivalences G to ZMod (2^(s+1)-1); or such an equivalence to "
                + "Fin (2*s) -> F2; or such an equivalence to (Fin (2*s-2) -> R) times ZMod 4. "
                + "The printed survey has R equal to the integers in its last family; the "
                + "companion paper gives the intended finite family with R equal to F2."),
            Entry("bajnok-classification-claim", "claim", "Conjecture 22 as printed", DescribeRole.Definition,
                "claim is the following closed proposition. For every G : Type with AddCommGroup G, "
                + "Fintype G and DecidableEq G, and all naturals m,s with 2 <= m and 2 <= s, "
                + "there exists A : Finset G with A.card = m and IsPerfectRestrictedBasis s A "
                + "if and only if ListedFamily G s m Int. Decidable equality supplies the finite-set "
                + "representation. The final integer-power family is retained literally."),
            Entry("golay-outside-bajnok-families", "golay_counterexample", "Both readings fail for the same group", DescribeRole.Theorem,
                "There exists A : Finset GolayGroup with A.card = 23, IsPerfectRestrictedBasis 3 A, "
                + "not ListedFamily GolayGroup 3 23 Int, and not ListedFamily GolayGroup 3 23 F2. "
                + "The proposed finite orders are 2^23, 15 and 64, all different from 2048; "
                + "the literal integer-power last family is infinite. The parameters also answer "
                + "Bajnok--Berson--Just Question 11 affirmatively, since 23 >= 2*3+2."),
            Describe.Lean(DescribeId.Create("bajnok-golay-classification-refuted"),
                DeclarationHandle.Create(Owner + "result"), H("The classification is false"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("result has type Not claim. Apply the necessary direction "
                    + "of the proposed equivalence to GolayGroup, m = 23 and s = 3. The perfect "
                    + "restricted basis gives a listed family, contradicting the counterexample. "
                    + "The obstruction also excludes the intended finite final family, so the "
                    + "refutation does not rely on its printed missing subscript."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bajnok-2022-perfect-restricted-bases-conjecture-22-golay"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock.Describe Entry(string id, string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
