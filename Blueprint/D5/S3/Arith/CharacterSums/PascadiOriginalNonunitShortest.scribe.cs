using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalNonunitShortestDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original unit-middle words whose actual reduced shortest vector is nonunit contribute at most an absolute constant times (XY)^2/p^4.",
        H("Original nonunit shortest-vector charts"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-original-nonunit-shortest-tuples"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalNonunitShortest.actual_nonunit_shortest_tuple_count"),
                H("The complete nonunit-shortest-vector contribution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let p be prime and let X,Y,H be positive real numbers with X<=Y, H^2=XY, p^3<=XY, 2X<p^2, 2Y<p^3 and Y<p^2. Fix the two original alternating units modulo p cubed. Let T be any finite set of original integer six-letter rows in the literal widths whose actual return word is minus the identity, with both middle letters units. For each row choose a reduced basis of its actual middle congruence lattice, and suppose p divides the first coordinate of the chosen shortest vector. Then |T|<=66048*(XY)^2/p^4.")),
                    Paragraph(Text("Divide each chosen shortest vector R by p. The original middle letters are units, so p divides both coordinates of R. The literal unit anchor and Y<p^2 exclude axis vectors. Reduction gives weighted squared length Q(R)<=2p^3, so U=R/p satisfies Q(U)<=2p. Both coordinates of U are units modulo p squared: otherwise the lattice relation forces both to be divisible by p, contradicting 2|U1*U2|<=Q(U). The entire nonaxis anisotropic ball contains at most 8p possible U. For fixed U the full slope modulo p cubed has at most p lifts, because its reduction modulo p squared is forced by U. The actual label image therefore has at most 8p squared elements.")),
                    Paragraph(Text("Rows with the same full slope share one actual lattice. The determinant of its nonunit shortest vector with the unit anchor is a nonzero multiple of p cubed; the weighted determinant inequality yields H/sigma<=2XY/p^3. Thus the union F of all actual middle points and endpoint points in this label fiber has at most 64XY/p^3 elements. There are at most |F| literal middle parameters. For each such parameter, the complete elementary return-word fiber estimate counts at most 2|F|+1 endpoint pairs, and the endpoints with the middle point reconstruct all six original integers. Since XY>=p^3, the label fiber has at most 8256*(XY/p^3)^2 rows. Summing the actual label fibers gives the stated bound."))),
                DescribeRole.Theorem),
            Paragraph(Text("The selected basis is geometric data for the original congruence lattice. No parameter-cardinality or endpoint-cardinality bound is assumed. This theorem counts the nonunit shortest-vector layer; the unit-shortest short range and nonunit endpoints in unit-right-side charts remain separate contributions.")))));
}
