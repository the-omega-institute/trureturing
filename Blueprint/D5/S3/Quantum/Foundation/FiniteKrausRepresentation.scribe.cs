using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;
internal sealed class FiniteKrausRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite rectangular completely positive matrix map has a finite Kraus witness.",
        H("Finite Kraus Representations"), Blocks(
            Paragraph(Text("Use the output-input order for the Choi coordinates: the channel acts on the first factor of the unnormalized maximally entangled projector. The finite Kraus family has rectangular output-by-input matrices; the zero map is included. Trace preservation is equivalent to the sum of the adjoint-Kraus products being the identity: cyclicity proves sufficiency, and testing every matrix unit proves necessity.")),
            Paragraph(Text("Ordinary transposition preserves positive matrices but is not completely positive. Its Choi matrix is the swap. On two qubits the partial transpose of the normalized Bell density is half the swap, with three eigenvalues equal to one half and one equal to minus one half. The antisymmetric vector detects the negative direction. Positivity on inputs alone therefore does not replace positivity with every auxiliary interface.")),
Describe.Lean(
            DescribeId.Create("finite-kraus-representation"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausRepresentation.exists_kraus"),
            H("Complete positivity gives a rectangular Kraus family"),
            StatementSource.FromAuthor(Disp(Seq(Operatorname, Grp(F.Id("IsCompletelyPositive")), Open, F.Id("Phi"), Close, Sp, Rightarrow, Sp, Exists, Sp, F.Id("M"), Comma, Sp, F.Id("Phi"), Eq, Operatorname, Grp(F.Id("ofKraus")), Open, F.Id("M"), Comma, F.Id("M"), Close, Dot))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/watrous2018theory")), Blocks(
                Paragraph(Text("For finite coordinate types A and B with decidable equality and an RCLike scalar, every completely positive rectangular MatrixMap Φ has a witness family M indexed by B × A and equals the associated Kraus sum (ofKraus denotes the Lean function of_kraus). This is a CP representation statement; it does not assert trace preservation.")),
                Paragraph(Text("The declaration is the selected upstream Physlib result at immutable revision 6a09b2d1761a0d4430083045a247eb121d8da260, routed from QuantumInfo/Channels/MatrixMap.lean and Unbundled.lean. Finite and decidable assumptions are retained explicitly."))),
            DescribeRole.Theorem))));
}
