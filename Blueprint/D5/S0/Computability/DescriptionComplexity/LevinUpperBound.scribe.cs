using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class LevinUpperBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite scaled-Kraft mass with a complexity ceiling bounds the candidate count.",
        H("Levin Upper Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("levin-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/LevinUpperBound.levin_upper_bound"),
                H("A scaled Kraft ceiling bounds the candidate count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Bar, new Formula.Subscript(F.Id("C"), F.Id("Q")), Open, F.Id("R"), Close, Bar,
                    Sp, Le, Sp, new Formula.Power(D(2), Seq(
                        F.Id("Q"), Sp, Minus, Sp, F.Id("K"), Open, F.Id("y"), Bar,
                        F.Id("x"), Close, Sp, Plus, Sp, F.Id("c"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source's prefix-machine argument selects one shortest witness for each "
                        + "candidate, assigns every witness a budget-scaled power-of-two weight, and "
                        + "then applies the conditional coding ceiling. This declaration exposes those "
                        + "two numerical premises directly.")),
                    Paragraph(Text(
                        "The lower-weight premise says every candidate contributes at least 2^K after "
                        + "scaling; the total-weight premise says the entire finite family is at most "
                        + "2^(Q + overhead). Natural-number factorization then gives the displayed "
                        + "cardinality bound. Universal-machine and conditional-complexity semantics are "
                        + "kept as upstream data rather than re-proved here.")),
                    Paragraph(Text(
                        "Mathlib's Kraft inequality and finite-program results were checked first, but "
                        + "no matching universal-machine model is present. The Lean proof therefore "
                        + "reuses only finite sums, power factorization, and Nat cancellation."))),
                DescribeRole.Theorem)),
        []));
}
