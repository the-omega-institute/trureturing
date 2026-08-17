using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Runtime;

internal sealed class FiniteRuntimeStateCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite runtime state components have multiplicative joint cardinality.",
        H("Finite Runtime State Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-runtime-components-have-multiplicative-cardinality"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Runtime/FiniteRuntimeStateCardinality."
                        + "finite_runtime_state_cardinality"),
                H("Finite runtime components have multiplicative cardinality"),
                StatementSource.FromAuthor(CardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C, K, R, M, and S be finite component state types. Their joint "
                            + "runtime state is the product type C times K times R times M times "
                            + "S, and its number of states is the product of the five component "
                            + "cardinalities.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle returned the exact binary theorem "
                            + "Fintype.card_prod. The Lean proof applies it repeatedly and uses "
                            + "natural-number multiplication associativity only to normalize "
                            + "the result. Repository search found uses of the binary theorem "
                            + "but no equivalent five-component statement. LeanSearch returned "
                            + "HTTP 404 and supplied no search conclusion.")),
                    Paragraph(Text(
                        "This closes only the finite-state cardinality clause of qdo-v1 "
                            + "theorem/21.1. It does not formalize the source's separate runtime "
                            + "modeling assumptions or its parameter-space bound."))),
                DescribeRole.Theorem))));

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula Fintype(Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, type, CloseBracket);

    private static Formula CardinalityFormula()
    {
        Formula c = F.Id("C");
        Formula k = F.Id("K");
        Formula r = F.Id("R");
        Formula m = F.Id("M");
        Formula s = F.Id("S");

        return Disp(Seq(
            Forall, Sp, c, Comma, Sp, k, Comma, Sp, r, Comma, Sp, m, Comma, Sp, s, Comma, Esc,
            Fintype(c), Sp, Fintype(k), Sp, Fintype(r), Sp, Fintype(m), Sp, Fintype(s),
            Comma, Esc,
            Card(Seq(c, Sp, Times, Sp, k, Sp, Times, Sp, r, Sp, Times, Sp, m, Sp, Times, Sp, s)),
            Sp, Eq, Sp,
            Card(c), Sp, Times, Sp, Card(k), Sp, Times, Sp, Card(r), Sp, Times, Sp, Card(m),
            Sp, Times, Sp, Card(s), Dot));
    }
}
