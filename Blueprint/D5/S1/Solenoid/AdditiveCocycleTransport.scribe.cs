using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class AdditiveCocycleTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Homomorphic images turn multiplicative cocycle identities into additive ones.",
            H("Additive Transport of a Multiplicative Cocycle"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("multiplicative-cocycle-maps-to-an-additive-cocycle"),
                    DeclarationHandle.Create(
                        "D5/S1/Solenoid/AdditiveCocycleTransport.map_cocycle_to_additive"),
                    H("The transported cocycle law is additive"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, F.Id("G"), Comma, Sp, F.Id("A"), Comma, Esc,
                        OpenBracket, Operatorname, Grp(F.Id("Monoid")),
                        Open, F.Id("G"), Close, CloseBracket, Comma, Esc,
                        OpenBracket, Operatorname, Grp(F.Id("AddMonoid")),
                        Open, F.Id("A"), Close, CloseBracket, Comma, Esc,
                        Forall, Sp, F.Id("f"), Colon, Sp, F.Id("G"), Sp,
                        To, Caret, Grp(Star), Sp,
                        Operatorname, Grp(F.Id("Multiplicative")),
                        Open, F.Id("A"), Close, Comma, Esc,
                        Forall, Sp,
                        F.Id("k"), Underscore, Grp(Alpha, GammaLower), Comma, Sp,
                        F.Id("k"), Underscore, Grp(Alpha, Beta), Comma, Sp,
                        F.Id("k"), Underscore, Grp(Beta, GammaLower), InMacro, Sp,
                        F.Id("G"), Comma, Esc,
                        F.Id("k"), Underscore, Grp(Alpha, GammaLower), Eq,
                        F.Id("k"), Underscore, Grp(Alpha, Beta), Sp, Star, Sp,
                        F.Id("k"), Underscore, Grp(Beta, GammaLower), Sp,
                        Rightarrow, Sp,
                        Operatorname, Grp(F.Id("toAdd")), Open,
                        F.Id("f"), Open,
                        F.Id("k"), Underscore, Grp(Alpha, GammaLower),
                        Close, Close, Eq,
                        Operatorname, Grp(F.Id("toAdd")), Open,
                        F.Id("f"), Open,
                        F.Id("k"), Underscore, Grp(Alpha, Beta),
                        Close, Close, Plus,
                        Operatorname, Grp(F.Id("toAdd")), Open,
                        F.Id("f"), Open,
                        F.Id("k"), Underscore, Grp(Beta, GammaLower),
                        Close, Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For any monoid-valued cocycle, a homomorphism into the "
                            + "multiplicative type tag of an additive monoid sends the direct "
                            + "transition to the sum of the two successive transitions.")),
                        Paragraph(Text(
                            "This declaration closes only the additive-transport continuation "
                            + "of the existing throat-transition cocycle. It assumes the "
                            + "multiplicative cocycle identity and proves its additive image; "
                            + "it makes no new existence or uniqueness claim for local lifts.")),
                        Paragraph(Text(
                            "The pinned library supplies the complete proof mechanism: map_mul "
                            + "preserves the product, and Multiplicative.toAdd_mul identifies "
                            + "multiplication in the tagged codomain with addition. The Lean "
                            + "declaration is a thin wrapper around those laws."))),
                    DescribeRole.Theorem))));
}
