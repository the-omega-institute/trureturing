using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class InterchangeDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete inverse-product interchange",
        H("Complete inverse-product interchange"),
        Blocks(
            Paragraph(Text("The simple-pole Ward relation [J[z],A[t]]=A0[z+t] cancels the eight ordered compositions in the two nested residues. The surviving diagonal terms are combined with the supported residue convolution. Thus R(A,R(J,B,d),r)=R(J,R(A,B,r),d)-R(A0,B,r+d), for signed r and d.")),
            Paragraph(Text("Finite inverse products are padded only above certified complete-residue cutoffs. Independent cutoffs for (A,B), (J,B) and (A0,B) yield new certified cutoffs for (A,Q(J,B)) and (J,Q(A,B)). The finite half-binomial convolution then changes the first shift s to s+1 in the correction. The result is Q(A,Q(J,B,1,d),s,r)=Q(J,Q(A,B,s,r),1,d)-Q(A0,B,s+1,r+d). Every cutoff is re-certified for the changed field.")),
            Paragraph(Text("The Ward relation is supplied by the native projected-ground theorem in NativeDefect. This general algebraic helper does not assume an original-source compatibility law.")))));
}
