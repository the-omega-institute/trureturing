using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class SemanticLayerShiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Computability/SemanticLayerShift",
            "A traceable semantic entry shifts losslessly to an open entry at the next layer."),
        H("Semantic Entries Reopen at the Next Layer"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("semantic-layer-shift-is-bijective"),
                H("The semantic layer shift is bijective"),
                LeanTheorem(
                    "D5/S0/Computability/SemanticLayerShift."
                    + "semantic_layer_shift_bijective"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("Bijective")), Open,
                    F.Id("semanticLayerShiftEquiv"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "A current-layer ledger entry whose detector has a semantic type "
                        + "mismatch is shifted into an open entry at the next layer. Source, "
                        + "detector, and future-budget types are connected by explicit "
                        + "equivalences, while the status transposition exchanges semantic "
                        + "and open and leaves closed and tail fixed. Restricting this full "
                        + "ledger equivalence to the two status fibers gives the typed layer "
                        + "shift. Bijectivity records the source atom's traceability demand: "
                        + "no entry is lost and no duplicate is introduced during reopening.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before implementation. It provides "
                        + "Equiv.swap for the status transposition, Equiv.subtypeEquiv for "
                        + "restricting an equivalence to matching predicates, and "
                        + "Equiv.bijective for the final theorem. It has no declaration for "
                        + "this ledger-specific semantic-to-open transition, so the Lean "
                        + "module constructs only that local equivalence and delegates its "
                        + "bijectivity to Mathlib. The claim is structural and carries no "
                        + "numerical certificate.")))
            ))));
}
