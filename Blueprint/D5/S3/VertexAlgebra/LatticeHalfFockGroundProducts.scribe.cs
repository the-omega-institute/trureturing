using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockGroundProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cocycle products in the actual chosen quotient ground module", H("Native Ground Products"), Blocks(
            Paragraph(Text("D is an arbitrary finite integral symmetric even-diagonal lattice datum and hu:IsUnit D.G.det. "
                + "groundRank and groundRepresentation are exactly the choices from actual_twisted_ground_representation D hu. "
                + "No alternative finite sign representation or charge table is substituted. "
                + "The actual central element acts by minus the identity; natural powers and native complexSign supply its general action.")),
            Describe.Lean(DescribeId.Create("actual-ground-cocycle-product"),
                DeclarationHandle.Create(Prefix + "ground_action_product"), H("Native cocycle product"),
                StatementSource.FromAuthor(Disp(Call("GroundProduct", F.Id("D"), F.Id("hu"), F.Id("a"), F.Id("b")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Exactly U_a U_b=epsilon(D,a,b) U_(a+b), from multiplication in the actual extension and quotient representation. "
                    + "The companion actual interchange is U_a U_b=paritySign(B(a,b)) U_b U_a. "
                    + "The half-norm square sign is retained. Quotient equality U_(-a)=U_a is a separate mod-two fact, not inversion. "
                    + "These ground relations do not themselves construct a twisted module or orbifold VOA. "
                    + "Classical provenance, zero novelty claim; full moonshine, string and AdS/CFT realization remain open."))), DescribeRole.Theorem))));
}
