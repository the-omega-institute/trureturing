using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;
internal sealed class RelativeSemanticDiagonalDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Complete decoder catalogs yield diagonal targets outside the latent closure.",H("Relative Semantic Diagonal"),Blocks(Describe.Lean(DescribeId.Create("complete-catalog-diagonal-is-blind"),DeclarationHandle.Create("D5/S3/ConceptDynamics/DefinitionEscape/RelativeSemanticDiagonal.complete_catalog_diagonal_blindResidual_nonempty"),H("A complete decoder catalog leaves a nonempty blind residual"),StatementSource.FromAuthor(Formula()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The diagonal target uses languageExtension, a decoder catalog, and a fixed-point-free twist; blindResidual remains canonical.")),Paragraph(Text("Surjectivity puts every decoder at an address where the diagonal differs, and the recovery criterion turns inadequacy into a nonempty blind residual."))),DescribeRole.Theorem))));
 private static Formula Formula(){var g=F.Id("Gamma");var c=F.Id("current");var twist=F.Id("twist");var catalog=F.Id("decoderCatalog");var t=Call("relativeSemanticDiagonal",twist,Call("languageExtension",c,Call("familyReadout",g)),catalog);return Disp(Seq(Forall,Sp,catalog,Colon,Sp,F.Id("X"),Sp,To,Sp,Open,F.Id("Current"),Sp,Times,Sp,Open,g,Sp,To,Sp,F.Id("InputOutput"),Close,Close,Sp,To,Sp,F.Id("Output"),Comma,Sp,Call("Nonempty",F.Id("X")),Sp,Land,Sp,Call("FixedPointFree",twist),Sp,Land,Sp,Call("Surjective",catalog),Sp,Rightarrow,Sp,Call("Nonempty",Call("blindResidual",g,c,t)),Dot));}
}
