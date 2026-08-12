using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class ConditionalComplexityFloorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty class with bounded realizing programs gives a conditional complexity floor.",
        H("Conditional Complexity Floor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-complexity-floor"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/ConditionalComplexityFloor.conditional_complexity_floor"),
                H("A bounded realizing program gives the floor inequality"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("BudgetedRealizers")),
                    Open, F.Id("realizes"), Comma, Sp, F.Id("length"), Comma, Sp,
                    F.Id("Q"), Close, Close, Sp,
                    Land, Sp,
                    Open, Forall, Sp, F.Id("f"), Comma, Sp, F.Id("p"), Comma, Sp,
                    F.Id("realizes"), Open, F.Id("f"), Comma, Sp, F.Id("p"), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("conditionalComplexity"), Sp, Le, Sp,
                    F.Id("length"), Open, F.Id("p"), Close, Sp, Plus, Sp, F.Id("c"), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("conditionalComplexity"), Sp, Minus, Sp, F.Id("c"),
                    Sp, Le, Sp, F.Id("Q"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "BudgetedRealizers contains exactly those class members having a realizing "
                        + "program whose natural-number length is at most Q. Nonemptiness therefore "
                        + "supplies both a member and a bounded witness program.")),
                    Paragraph(Text(
                        "The fixed-overhead compiler premise records the source decoding construction: "
                        + "every realizing program yields a conditional description whose length is at "
                        + "most the program length plus c. Applying it to the extracted witness and then "
                        + "using the budget gives the displayed floor inequality.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. It has no conditional-description "
                        + "complexity abstraction matching this statement. The proof reuses "
                        + "Nat.sub_le_iff_le_add for the final natural-number subtraction step; the "
                        + "realization and compiler semantics remain explicit parameters."))),
                DescribeRole.Theorem)),
        []));
}
