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
        var a = Id("a");
        var y = Id("y");
        var address = Id("A");
        var alphabet = Id("Y");
        var type = new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
        var boolean = new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
        var unit = new Formula.NamedConstant(FormulaIdentifier.Create("Unit"));
        var listingType = new Formula.TypeArrow(
            address, new Formula.TypeArrow(address, alphabet));
        Formula.BoundVariable[] parameters =
        [
            new(FormulaIdentifier.Create("A"), new Formula.Subscript(type, Id("u"))),
            new(FormulaIdentifier.Create("Y"), new Formula.Subscript(type, Id("v"))),
            new(FormulaIdentifier.Create("f"), new Formula.TypeArrow(alphabet, alphabet)),
            new(FormulaIdentifier.Create("g"), listingType),
        ];

        var fixedPointFree = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("y"), alphabet)],
            NotEqual(Call("f", y), y));

        var escaped = Call("IsEscaped", f, g);

        var lawvereCore = new Formula.Logic(
            fixedPointFree, FormulaLogicOperator.Implies, escaped);
        var lawvere = new Formula.BindMany(
            FormulaQuantifier.ForAll, [.. parameters], lawvereCore);

        var captured = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("p"), new Formula.TypeArrow(boolean, boolean)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("q"),
                    new Formula.TypeArrow(unit, new Formula.TypeArrow(unit, boolean))),
            ],
            new Formula.Not(Call("IsEscaped", Id("p"), Id("q"))));

        var negation = F.Seq(
            F.Open, Id("b"), F.Colon, F.Sp, boolean, F.Close, F.Sp,
            F.Mapsto, F.Sp, F.Bang, Id("b"));
        var constantTrue = F.Seq(
            F.Open, Id("x"), F.Colon, F.Sp, unit, F.Close, F.Sp, F.Mapsto, F.Sp,
            F.Open, Id("z"), F.Colon, F.Sp, unit, F.Close, F.Sp, F.Mapsto, F.Sp,
            new Formula.NamedConstant(FormulaIdentifier.Create("true")));
        var escapedWitness = Call("IsEscaped", negation, constantTrue);

        var pointwiseDiagonal = new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("a"), address,
            Equal(Call("diagonal", f, g, a), Call("f", Call("g", a, a))));
        var escapeIffOutsideRange = new Formula.Logic(
            escaped, FormulaLogicOperator.Iff,
            new Formula.Not(F.Seq(
                F.Open,
                new Formula.Relation(
                    Call("diagonal", f, g), FormulaRelationOperator.MemberOf, Call("range", g)),
                F.Close)));
        var everyListingEscapes = new Formula.Logic(
            fixedPointFree, FormulaLogicOperator.Implies,
            new Formula.Bind(
                FormulaQuantifier.ForAll, FormulaIdentifier.Create("h"), listingType,
                Call("IsEscaped", f, Id("h"))));
        var package = new Formula.BindMany(
            FormulaQuantifier.ForAll, [.. parameters],
            new Formula.Logic(pointwiseDiagonal, FormulaLogicOperator.And,
                new Formula.Logic(escapeIffOutsideRange, FormulaLogicOperator.And,
                    new Formula.Logic(everyListingEscapes, FormulaLogicOperator.And, captured))));

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
                Paragraph(Text(
                    "The universe levels u and v are arbitrary and independent. In the "
                        + "quantifiers below, membership in a type denotes a Lean typed binder; "
                        + "arrows denote full function spaces. Application is curried: g(a, b) "
                        + "means g a b, and diagonal(f, g, a) means diagonal f g a. The notation "
                        + "range(g) denotes Set.range g, a set of functions from A to Y. "
                        + "Bool is Lean's two-value type with values true and false; Unit is "
                        + "Lean's one-value type with value (). In the explicit witness, ! is "
                        + "Boolean negation (Bool.not), and true is the Bool value, not the "
                        + "proposition True. The existential variables p and q name the Bool "
                        + "twist and Unit listing independently of the outer f and g.")),
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
                        "The witnesses are p = id on Bool and q = fun _ _ => true on Unit. "
                            + "This listing is captured, which "
                            + "shows the fixed-point-free premise carries weight."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("escape-is-attained-on-a-two-symbol-alphabet"),
                    DeclarationHandle.Create(
                        declarationPrefix + "not_escaped_isEscaped_witness"),
                    H("Escape is attained on a two-symbol alphabet"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(escapedWitness)),
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
