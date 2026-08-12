using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class GraphPairingCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A graph pairing separates both curried coordinates exactly under injectivity and a one-point omission bound.",
        H("Graph Pairing Separation Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("graph-pairing-separating-iff"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/GraphPairingCriterion.graph_pairing_separating_iff"),
                H("Graph pairing separates both coordinates exactly under the range criterion"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, Sp, F.Id("B"), Comma, Sp,
                    F.Id("f"), Colon, Sp, F.Id("A"), Sp, To, Sp, F.Id("B"), Comma, RowBreak,
                    Open,
                    Operatorname, Grp(F.Id("Injective")), Open,
                    F.Id("a"), Sp, Mapsto, Sp, Open,
                    F.Id("b"), Sp, Mapsto, Sp,
                    F.Id("f"), Open, F.Id("a"), Close, Sp, Eq, Sp, F.Id("b"), Close, Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Injective")), Open,
                    F.Id("b"), Sp, Mapsto, Sp, Open,
                    F.Id("a"), Sp, Mapsto, Sp,
                    F.Id("f"), Open, F.Id("a"), Close, Sp, Eq, Sp, F.Id("b"), Close, Close,
                    Close, Sp, Iff, Sp, Open,
                    Operatorname, Grp(F.Id("Injective")), Open, F.Id("f"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Subsingleton")), Open,
                    F.Id("B"), Sp, Setminus, Sp,
                    Operatorname, Grp(F.Id("range")), Open, F.Id("f"), Close, Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary types A and B and a function f from A to B, consider the relation "
                        + "that holds on (a,b) exactly when f(a) = b. Injectivity of its row curry says "
                        + "that distinct inputs have distinct graph rows. Injectivity of its column curry "
                        + "says that distinct codomain points have distinct graph columns.")),
                    Paragraph(Text(
                        "Both separation properties hold exactly when f is injective and the complement of "
                        + "its range is a subsingleton. Thus at most one codomain point may be omitted. The "
                        + "forward proof reads injectivity from equal rows and compares any two omitted "
                        + "columns; the reverse proof uses an attained point to distinguish columns unless "
                        + "both lie outside the range.")),
                    Paragraph(Text(
                        "This is the graph-pairing clause only. Other clauses carried by the source atom are "
                        + "not claimed by this deposit and remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
