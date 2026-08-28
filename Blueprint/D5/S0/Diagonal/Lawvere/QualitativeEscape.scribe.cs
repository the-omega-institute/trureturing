using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Lawvere;

internal sealed class QualitativeEscapeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Lawvere =
        LibraryNoteRef.Create("D5/L/Diagonal/lawvere1969diagonal");

    public DocumentDefinition Create()
    {
        var f = Id("f");
        var g = Id("g");
        var y = Id("y");
        var address = Id("A");
        var alphabet = Id("Y");
        var type = F.Seq(F.Operatorname, F.Grp(Id("Type")));

        var fixedPointFree = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("y"), alphabet)],
            NotEqual(Call("f", y), y));

        var escaped = Call("IsEscaped", f, g);

        var lawvereCore = new Formula.Logic(
            fixedPointFree, FormulaLogicOperator.Implies, escaped);
        var lawvere = F.Seq(
            F.Forall, F.Sp, address, F.Comma, F.Sp, alphabet, F.Colon, F.Sp, type,
            F.Comma, F.Sp,
            f, F.Colon, F.Sp, new Formula.TypeArrow(alphabet, alphabet), F.Comma, F.Sp,
            g, F.Colon, F.Sp,
            new Formula.TypeArrow(address, new Formula.TypeArrow(address, alphabet)),
            F.Comma, F.Sp,
            lawvereCore);

        var captured = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("f"), Id("Y0")),
                new Formula.BoundVariable(FormulaIdentifier.Create("g"), Id("L0")),
            ],
            new Formula.Not(escaped));

        var package = new Formula.Logic(lawvereCore, FormulaLogicOperator.And, captured);

        const string declarationPrefix = "D5/S0/Diagonal/Lawvere/QualitativeEscape.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "A fixed-point-free twist escapes every listing, with no finiteness hypothesis.",
            H("Lawvere Escape"),
            Blocks(
                Paragraph(Text(
                    "The self-application fragment reads a listing as a map sending each "
                        + "address to a function on addresses, applies a twist to the values "
                        + "sitting on the diagonal, and calls the listing escaped when the "
                        + "resulting function is absent from its range.")),
                Paragraph(Text(
                    "The qualitative half of Lawvere's fixed-point theorem is that a twist "
                        + "without a fixed point escapes every listing. The repository already "
                        + "reached that conclusion by counting, which needs both the address "
                        + "set and the alphabet to be finite. The argument below needs "
                        + "neither: a row that equals the twisted diagonal exhibits a fixed "
                        + "point at its own address, so no row can equal it.")),
                Paragraph(Text(
                    "The hypothesis is not decorative. On the two-symbol alphabet the identity "
                        + "twist fixes every point, and the constant listing at a single "
                        + "address is then captured rather than escaped, so the implication "
                        + "cannot be strengthened by dropping its premise.")),
                Describe.Lean(
                    DescribeId.Create("a-fixed-point-free-twist-escapes-every-listing"),
                    DeclarationHandle.Create(declarationPrefix + "escaped_of_fixedPointFree"),
                    H("A fixed-point-free twist escapes every listing"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(lawvere)),
                    AssessedProvenance.FromLiterature(Lawvere),
                    Blocks(Paragraph(Text(
                        "Suppose the twisted diagonal lies in the range of the listing, say as "
                            + "the row at some address. Evaluating that equality at the address "
                            + "itself makes the twist fix the diagonal entry there, "
                            + "contradicting the hypothesis. No finiteness is used."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("a-twist-with-a-fixed-point-captures-a-listing"),
                    DeclarationHandle.Create(
                        declarationPrefix + "exists_captured_listing_of_fixedPoint"),
                    H("A twist with a fixed point captures a listing"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(captured)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The identity twist on the two-symbol alphabet together with the "
                            + "constant listing at a one-point address set is captured, which "
                            + "shows the fixed-point-free premise carries weight."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("escape-is-attained-on-a-two-symbol-alphabet"),
                    DeclarationHandle.Create(
                        declarationPrefix + "not_escaped_isEscaped_witness"),
                    H("Escape is attained on a two-symbol alphabet"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(escaped)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The negation twist has no fixed point, so the constant listing on a "
                            + "one-point address set is escaped. Escape is therefore attained "
                            + "and the universal statement is not vacuous for want of "
                            + "listings."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-self-application-fragment-packaged"),
                    DeclarationHandle.Create(
                        declarationPrefix + "self_application_fragment_package"),
                    H("The self-application fragment packaged"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(package)),
                    AssessedProvenance.FromLiterature(Lawvere),
                    Blocks(Paragraph(Text(
                        "One conjunction carrying the fragment: the diagonal construction is "
                            + "pointwise the twist applied to the diagonal entries, escape is "
                            + "exactly absence of that diagonal from the range, a "
                            + "fixed-point-free twist escapes every listing, and the premise "
                            + "cannot be dropped."))),
                    DescribeRole.Theorem))));
    }
}
