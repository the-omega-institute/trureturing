using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class TotalCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Conventions/TotalCode",
                "Total-code-preserving transformations cannot hide object changes."),
            H("No Invisible Register"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("no-hidden-register"),
                    H("Preserving the total code preserves the object"),
                    LeanTheorem("D5/S0/Conventions/TotalCode.no_hidden_register"),
                    LatexStatement.Create(
                        @"$$\forall D,R,L,\quad "
                        + @"\left[\forall f:\operatorname{TotalCode}(D,R,L)"
                        + @"\to\operatorname{TotalCode}(D,R,L),\ "
                        + @"\left(\forall X,\ \operatorname{data}(f(X))="
                        + @"\operatorname{data}(X)\right)\land "
                        + @"\left(\forall X,\ \operatorname{rules}(f(X))="
                        + @"\operatorname{rules}(X)\right)\land "
                        + @"\left(\forall X,\ \operatorname{ledger}(f(X))="
                        + @"\operatorname{ledger}(X)\right)"
                        + @"\Rightarrow\forall X,\ f(X)=X\right]\land "
                        + @"\left[\forall f,X,\ f(X)\neq X\Rightarrow "
                        + @"\operatorname{data}(f(X))\neq\operatorname{data}(X)\lor "
                        + @"\operatorname{rules}(f(X))\neq\operatorname{rules}(X)\lor "
                        + @"\operatorname{ledger}(f(X))\neq\operatorname{ledger}(X)"
                        + @"\right].$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The semantic kernel-identity criterion is represented here by "
                        + "Lean structure equality, not claimed as a proof of an ontological "
                        + "identity criterion. Extensionality proves both the preservation "
                        + "clause and its componentwise dual. This is the C3a identity pillar "
                        + "announced for use in 23.4.")))))));
}
