using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Promotion;
internal sealed class ResearchPromotionLoopDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Ledgers prune; walls persist; release forces escape; promotion receipts are typed.",H("Research Promotion Loop"),Blocks(Describe.Lean(DescribeId.Create("released-anchor-has-typed-receipt"),DeclarationHandle.Create("D5/S3/ConceptDynamics/Promotion/ResearchPromotionLoop.released_anchor_has_receipt"),H("A released anchor projects its typed proof receipt and link chain"),StatementSource.FromAuthor(Formula()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("PromotionChain is typed bookkeeping from proposal through verdict, frozen node, released anchor, and research seed.")),Paragraph(Text("The proved verdict branch supplies the ProofReceipt and all faithfulness equalities; the refuted branch is excluded by IsReleased.")),Paragraph(Text("This is typed bookkeeping, not an empirical validity or promotion-policy theorem."))),DescribeRole.Theorem))));
 private static Formula Formula(){var c=F.Id("chain");var r=F.Id("receipt");return Disp(Seq(Exists,Sp,r,Colon,Sp,Call("ProofReceipt",Call("certifies",c),Call("exactStatement",c)),Comma,Sp,Call("verdict",c),Sp,Eq,Sp,Call("PromotionVerdictProved",r),Sp,Land,Sp,Call("exactStatement",c),Sp,Eq,Sp,Call("statementOfProposal",c),Sp,Land,Sp,Call("frozenNode",c),Sp,Eq,Sp,Call("nodeOfVerdict",c),Sp,Land,Sp,Call("releasedAnchor",c),Sp,Eq,Sp,Call("anchorOfFrozenNode",c),Sp,Land,Sp,Call("researchSeed",c),Sp,Eq,Sp,Call("seedOfReleasedAnchor",c),Dot));}
}
