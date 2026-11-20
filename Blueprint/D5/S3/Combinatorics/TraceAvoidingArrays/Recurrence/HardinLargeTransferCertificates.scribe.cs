using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinLargeTransferCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinLargeTransferCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source vector identities with exact integer lags.",
        H("Continuation polynomials"),
        Blocks(
            Node("row7-lags", "rowSevenCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 47 are (16, 196, −3074, −10566, 216596, 78746, −7555872, 9810518, 143284008, −357710825, −1495653319, 5688279614, 7841029858, −51325489356, −6388247723, 287774292823, −176104268208, −0xf329324f36, 0x11d53a7aba4, 0x23f76e32e2f, −0x3f99620d7b9, −0x352695bd558, 0x91834a724fc, 0x26af1398425, −0xe4e3e053fa0, 0x107f904a101, 0xfed1c63947e, −0x4cdafc801b8, −0xcad68e2a227, 0x60f61784666, 0x7302409faae, −0x4908fef0104, −0x2d86ef2526c, 0x24aedad60d0, 823313870004, −866028504844, −126258454484, 202072349924, 5321968504, −31031088088, 1747695584, 2945878288, −337788928, −153195552, 23841280, 3259008, −599040)."),
            Node("row7", "rowSeven", "Full-state relation at height 7", DescribeRole.Theorem,
                "On all 2187 unrestricted columns at height 7, the power at exponent 48 on ones equals the source lag-weighted sum of the power vectors at exponents 47 down to 1. The coefficient sum is one."),
            Node("column5-lags", "wordFiveCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 7 are (15, −59, 60, 21, −55, 21, −2)."),
            Node("column5", "wordFive", "Full-state relation at width 5", DescribeRole.Theorem,
                "On all 48 proper words at width 5, the power at exponent 7 on ones equals the source lag-weighted sum of the power vectors at exponents 6 down to 0. The coefficient sum is one."),
            Node("column6-lags", "wordSixCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 10 are (19, −74, −25, 361, −268, −271, 337, −54, −29, 5)."),
            Node("column6", "wordSix", "Full-state relation at width 6", DescribeRole.Theorem,
                "On all 96 proper words at width 6, the power at exponent 10 on ones equals the source lag-weighted sum of the power vectors at exponents 9 down to 0. The coefficient sum is one."),
            Node("column7-lags", "wordSevenCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 20 are (42, −590, 3167, −1918, −37505, 95138, 67348, −449955, 266387, 629595, −841378, −28007, 588908, −332461, 7999, 44409, −11184, −342, 380, −32)."),
            Node("column7", "wordSeven", "Full-state relation at width 7", DescribeRole.Theorem,
                "On all 192 proper words at width 7, the power at exponent 20 on ones equals the source lag-weighted sum of the power vectors at exponents 19 down to 0. The coefficient sum is one."),
            Paragraph(Text("The verified multiset of successor classes gives the exact quotient action on each actual state. The checked power table begins at one on every class, and each row is obtained by multiplying by its quotient matrix. The final vector relation pulls back through the class map to the actual source states.")),
            Paragraph(Text(
                "For the height-five row of A233174 and A233178, HardinA233178Recurrence.result proves "
                + "the recurrence for the literal normalized array count T(5,n) for every n at least 12. "
                + "Its source count fixes the first cell to zero, uses the same earlier-occurrence restrictions "
                + "in row-major order, and uses the horizontal, diagonal and antidiagonal bonds between "
                + "successive columns. The lag-j multiplier is 32^j times the jth entry of "
                + "(6, 31, −97, −163, 417, 93, −514, 192, 72, −36).")),
            Paragraph(Text(
                "HardinA233178Chromatic.result gives the corresponding relation for every linear readout "
                + "of the three-label continuation vectors. Its base-three indexing enumerates all 243 "
                + "source columns, and its bond is the C5 bond on decoded columns. Taking a readout supported "
                + "at each individual column and setting the shift to zero gives the full-state identity "
                + "at exponent 11 with lagged exponents 10 down to 1. The coefficients sum to one. "
                + "HardinActualTransfers.column_continuations identifies each power-vector entry with the "
                + "continuation count from its specified first column. For n at least 2, "
                + "HardinA233178Literal.chromatic_source_count gives 48 T(5,n) = 32^n (L(n) + 6). "
                + "Here L(n) sums the continuations at exponent n − 1 over all first columns.")),
            Paragraph(Text(
                "For the height-seven row of A233174 and the order-47 formula linked from A233180, let T(7,n) "
                + "count literal row-major normalized arrays with horizontal bonds and both diagonal bonds. "
                + "HardinThinGraphTransport.literalEquiv identifies these arrays with the normalized graph colourings. "
                + "For n at least 2 the graph is connected and bipartite by column parity, so "
                + "HardinGraphNormalization.connected_count gives 48 T(7,n) = 128^n (L(n) + 6), where L(n) "
                + "counts the proper three-colourings. HardinColumnContinuations.coloringEquiv reads each colouring "
                + "as a sequence of columns. HardinActualTransfers.column_count sums the C7 power on ones at "
                + "exponent n − 1 over all 2187 unrestricted first columns.")),
            Paragraph(Text(
                "For every natural n at least 49, apply C7^(n − 49) to the height-seven vector relation "
                + "and sum the entries. The left exponent becomes n − 1 and the right exponent at lag j "
                + "becomes n − j − 1. The coefficient sum is one, so L(n) + 6 satisfies the same relation. "
                + "Since n − j is at least 2 for each j from 1 through 47, the connected-strip formula applies "
                + "to every term. Substituting it and using 128^n = 128^j 128^(n − j) gives "
                + "T(7,n) = sum over j from 1 through 47 of 128^j c_j T(7,n − j), using the signed coefficients above.")),
            Paragraph(Text(
                "For the width-seven column of A233174, let T(m,7) count the literal row-major normalized "
                + "arrays of height m and width seven. The first row has three choices of initial pair label "
                + "and two choices at each of the six following positions, giving 192 proper words. In R7, "
                + "the transition from one such word to another requires unequal labels across each of the two "
                + "diagonals between successive rows. HardinThinGraphTransport.colouringEquiv reads proper "
                + "three-colourings as row sequences, and HardinActualTransfers.word_continuations gives the "
                + "number of tails with any specified first word. Summing over all first words gives "
                + "L(m) = 1ᵀ R7^(m − 1) 1 for every m at least 1.")),
            Paragraph(Text(
                "HardinThinGraphTransport.literalEquiv uses the row-major order to identify the literal arrays "
                + "with legal graph colourings. HardinGraphNormalization.literalPartitionEquiv describes those "
                + "colourings by independent-set partitions and free choices within the complementary pairs. "
                + "At width seven, the strip has an edge and is connected and bipartite by column parity even "
                + "at height one. HardinGraphNormalization.connected_count gives 48 T(m,7) = 128^m (L(m) + 6) "
                + "for every m at least 1.")),
            Paragraph(Text(
                "For every natural m at least 21, apply R7^(m − 21) to the width-seven vector relation and sum "
                + "its entries. The left exponent is m − 1, and the exponent at lag j is m − j − 1. "
                + "The coefficients sum to one, so the resulting recurrence for L(m) also holds for L(m) + 6. "
                + "Since m − j is at least 1 for j from 1 through 20, the normalization formula applies at "
                + "every lag, including height one when m = 21 and j = 20. Factoring 128^m as 128^j times "
                + "128^(m − j) gives T(m,7) = sum over j from 1 through 20 of 128^j c_j T(m − j,7), "
                + "using the signed width-seven coefficients above."))
        )));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
