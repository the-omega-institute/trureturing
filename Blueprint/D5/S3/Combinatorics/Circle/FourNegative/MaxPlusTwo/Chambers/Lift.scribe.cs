using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers;
internal sealed class LiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural lift of actual centered sources",
        H("Inherited physical labels"),
        Blocks(Paragraph(Text("The internal inherited_source_lift applies source_shadow_charge at d and d+t and proves, for every original physical index i<a+b+c+d, that the actual charge at t+i is unchanged and its actual shadow is multiplied by 2^t. All four physical intervals and their negative final labels are included. The resulting inherited_old_lift proves f_lift(t+i)=2^t*f(i)-(2^t-1)*q(i). These statements use the actual centered definitions, not a hypothetical source interface. They have no coprimality, numerical injectivity or period condition. The prepended low-label source values and their exact geometric sum recover the prefix formula h_lift=2^t*h+(2^t-1)*Q for every bounded physical prefix. The internal natural_lift_strong joins the prepended low labels and every inherited prefix using the actual centered sources and actual nonnegative charge. natural_lift_strips supplies both centered strips on that same physical word, and natural_lift_totals proves the exact lifted old and charge totals from their base totals. These internal transport statements take the base strong path and complete base charge as premises. Completing the joint-order construction still requires proving them for every chamber of baseWord."))), []));
}
