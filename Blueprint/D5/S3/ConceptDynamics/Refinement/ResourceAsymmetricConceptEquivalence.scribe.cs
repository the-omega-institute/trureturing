using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class ResourceAsymmetricConceptEquivalenceDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Refinement/ResourceAsymmetricConceptEquivalence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite permutation can be concept-equivalent but resource-asymmetric.",
        H("Resource-Asymmetric Concept Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "ordinary-equivalence-does-not-imply-resource-equivalence"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "ordinary_equivalence_does_not_imply_resource_equivalence"),
                H("Ordinary concept equivalence need not be resource equivalence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a finite carrier, the two public concepts are the identity readout "
                            + "and the readout given by a named permutation. Its canonical inverse "
                            + "recovers the identity, so the concepts mutually factor.")),
                    Paragraph(Text(
                        "The resource premise uses one cost model and one budget. It places the "
                            + "forward permutation within that budget and its inverse outside the "
                            + "same budget.")),
                    Paragraph(Text(
                        "The forward map directly witnesses resource refinement in one direction. "
                            + "Any factor witnessing the reverse direction must equal the inverse "
                            + "permutation, so its alleged budget bound contradicts the premise.")),
                    Paragraph(Text(
                        "All three clauses are public: ordinary equivalence, positive forward "
                            + "resource refinement, and failed reverse resource refinement. The "
                            + "cost and refinement relations are imported family primitives."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("X");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula permutation = F.Id("pi");
        Formula inverse = Seq(permutation, Caret, Grp(Minus, D(1)));
        Formula cost = F.Id("cost");
        Formula budget = F.Id("r");
        Formula identity = F.Id("id");
        Formula forwardCost = Call("cost", permutation);
        Formula inverseCost = Call("cost", inverse);
        Formula ordinary = Call("ConceptEquivalent", identity, permutation);
        Formula forward = Call(
            "ResourceRefines", cost, budget, permutation, identity);
        Formula reverse = Call(
            "ResourceRefines", cost, budget, identity, permutation);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrier, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("Finite", carrier), CloseBracket,
            Comma, RowBreak, Grp(),
            Forall, Sp, permutation, Colon, Sp, carrier, Sp, Equiv, Sp, carrier,
            Comma, Sp, cost, Colon, Sp, F.Id("ResourceCost"), Comma, Sp,
            budget,
            Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            Open, forwardCost, Sp, Leq, Sp, budget, Sp, Land, Sp,
            Neg, Open, inverseCost, Sp, Leq, Sp, budget, Close,
            Close, Sp, Rightarrow, Sp,
            RowBreak, Grp(),
            Open, ordinary, Sp, Land, RowBreak, Grp(),
            forward, Sp, Land, RowBreak, Grp(),
            Neg, Open, reverse, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
