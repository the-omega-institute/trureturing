using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class SplitTowerTranslationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derive integer-time laws inside the actual recoding constructions.",
        H("Derive integer-time laws inside the actual recoding constructions"),
        Blocks(
            Paragraph(Text("time is StandardBeamHomeomorphisms.translate with coordinate t+a. On counted histories this has the same defining coordinates as NumberedPositiveInverseLaws.translate. The retained relabel and split forget laws commute with every signed time. The coordinate definitions give the corresponding lift laws, retaining t+1 for outgoing labels and t-1 for incoming labels.")),
            Paragraph(Text("The generic relabel and split laws quantify arbitrary Type* carriers. Relabel homeomorphism laws use discrete topological edge types. Positive laws quantify arbitrary nonnegative rectangular R,S with no period hypothesis. Applying the forward positive time law to the inverse image and canceling the bijection derives inverse time commutation locally.")),
            Paragraph(Text("These constructions and identities are repository-derived. Their provenance does not assert literature novelty.")),
            Describe.Remark(DescribeId.Create("positive-recoding-splittowertranslation-time"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.time"), H("time"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Use the existing graph-history translation, whose value at t reads the original history at t+a. This fixes the signed convention for all tower laws.")))),
            Describe.Remark(DescribeId.Create("positive-recoding-splittowertranslation-counted"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.counted"), H("counted"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Use the existing counted graph on numbered matrix edges. The adapter connects graph-history translation to the counted path API.")))),
            
            Describe.Remark(DescribeId.Create("positive-recoding-splittowertranslation-relabel-time"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_time"), H("relabel_time"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A graph relabel acts coordinatewise, so its history map commutes with every signed translation. The endpoint proofs do not alter time.")))),
            Describe.Remark(DescribeId.Create("positive-recoding-splittowertranslation-relabel-homeomorph-time"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_homeomorph_time"), H("relabel_homeomorph_time"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The relabel homeomorphism has the same coordinatewise time law under the declared discrete edge topologies.")))),
            Describe.Remark(DescribeId.Create("positive-recoding-splittowertranslation-relabel-inverse-time"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_inverse_time"), H("relabel_inverse_time"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The inverse relabel homeomorphism also commutes with every signed translation. This permits both chart maps to pass through a correction.")))),
            
            Describe.Remark(DescribeId.Create("positive-recoding-splittowertranslation-outgoing-forget-time"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.outgoing_forget_time"), H("outgoing_forget_time"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Outgoing forget applies the coordinatewise edge projection, so it commutes with the original signed translation.")))),
            
            Describe.Remark(DescribeId.Create("positive-recoding-splittowertranslation-incoming-forget-time"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.incoming_forget_time"), H("incoming_forget_time"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Incoming forget commutes with signed translation by its coordinate projection. No extra centring term is introduced.")))),
            Describe.Remark(DescribeId.Create("positive-recoding-splittowertranslation-positive-time"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.positive_time"), H("positive_time"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The counted positive recoding uses the same offset on its current S half and next R half. It therefore commutes with every signed translation.")))))));
}
