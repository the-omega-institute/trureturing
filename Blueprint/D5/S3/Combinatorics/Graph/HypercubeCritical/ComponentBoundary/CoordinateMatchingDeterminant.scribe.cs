using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class CoordinateMatchingDeterminantDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CoordinateMatchingDeterminant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A determinant coefficient from ordered coordinate matching",
        H("A determinant coefficient from ordered coordinate matching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coeff-det-of-diagonal-priority"),
                DeclarationHandle.Create(Module + ".coeff_det_of_diagonal_priority"),
                H("The coefficient at the diagonal multidegree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each nonzero entry of a square matrix is a scalar times the variable indexed by its priority. Write d(i) for the diagonal priority at i. Assume each nonzero off-diagonal entry (i,j) has priority strictly greater than d(i) or d(j). At the multidegree that counts each diagonal priority with multiplicity, the determinant coefficient equals the product of the diagonal scalars. If the scalars lie in a domain and all diagonal scalars are nonzero, the determinant is a nonzero polynomial.")),
                    Paragraph(Text("In the Leibniz expansion, discard any permutation with a zero factor. For a surviving nonidentity permutation, take the least diagonal priority k among the moved indices. The permutation maps moved indices to moved indices, so both endpoints of every moved entry have diagonal priority at least k. The entry condition forces its priority above k. Fixed indices contribute the same counts as the diagonal, and at least one moved diagonal entry contributes at k. The strictly smaller exponent at k excludes this permutation from the diagonal coefficient."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the signed weighted cube matrix, take the chosen support vertices as columns and the omitted vertices as available rows. In priority order, match every remaining column to its available row obtained by flipping the current coordinate, then remove the matched endpoints. Each flip is injective, so all pairs at that step can be taken simultaneously. If every column is matched, retain exactly the matched rows and index each by its matched column. If a nonzero off-diagonal entry at priority k had neither endpoint matched earlier, it would have been selected at step k. Its endpoints have different partners in the completed matching, so at least one was matched earlier. The retained square minor has diagonal scalars ±1, making its diagonal coefficient ±1.")),
            Paragraph(Text("The order-126 grid-projection archive records completed coordinate matchings for all 111 signed order-eighteen supports of maximum contact degree seven in the terminal census. Each matching certifies a nonzero polynomial minor by this theorem. Together with the universal weighted-singularity condition in the archived reduction, these minors exclude that branch of the 18+3 fold for a separated 126+132 candidate. The census and its matchings are external research evidence. The formal result is the determinant criterion used in the study of Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
        []));
}
