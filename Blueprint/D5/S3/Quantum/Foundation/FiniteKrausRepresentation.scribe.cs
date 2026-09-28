using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;
internal sealed class FiniteKrausRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite rectangular completely positive matrix map has a finite Kraus witness.",
        H("Finite Kraus Representations"), Blocks(Describe.Lean(
            DescribeId.Create("finite-kraus-representation"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausRepresentation.exists_kraus"),
            H("Complete positivity gives a rectangular Kraus family"),
            StatementSource.FromAuthor(Disp(Seq(Operatorname, Grp(F.Id("IsCompletelyPositive")), Open, F.Id("Phi"), Close, Sp, Rightarrow, Sp, Exists, Sp, F.Id("M"), Comma, Sp, F.Id("Phi"), Eq, Operatorname, Grp(F.Id("ofKraus")), Open, F.Id("M"), Comma, F.Id("M"), Close, Dot))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/watrous2018theory")), Blocks(
                Paragraph(Text("For finite coordinate types A and B with decidable equality and an RCLike scalar, every completely positive rectangular MatrixMap Φ has a witness family M indexed by B × A and equals the associated Kraus sum (ofKraus denotes the Lean function of_kraus). This is a CP representation statement; it does not assert trace preservation.")),
                Paragraph(Text("The declaration is the selected upstream Physlib result at immutable revision 6a09b2d1761a0d4430083045a247eb121d8da260, routed from QuantumInfo/Channels/MatrixMap.lean and Unbundled.lean. Finite and decidable assumptions are retained explicitly."))),
            DescribeRole.Theorem))));
}
