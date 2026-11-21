using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiAffineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiAffine.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each matching uses the chosen coordinate once, so its polynomial is at most linear in that coordinate.",
        H("Isolating a coordinate in a matching"),
        Blocks(
            Definition("Rest", "Remaining coordinates",
                "The remaining coordinate set omits the distinguished index."),
            Definition("Coeff", "Coefficient ring",
                "Coefficients are complex multivariate polynomials in the remaining coordinates."),
            Definition("isolate", "Single-variable presentation",
                "The chosen variable is extracted as the outer polynomial variable via the option-type decomposition."),
            Theorem("isolate_X_self", "The distinguished variable",
                "The variable at the chosen index becomes the outer indeterminate.",
                IsolateXSelf()),
            Theorem("isolate_X_other", "A remaining variable",
                "For a proof h of j ≠ w, the pair ⟨j, h⟩ indexes a variable in Rest(w), so its variable belongs to Coeff(w). Polynomial.C embeds that coefficient as a constant outer polynomial.",
                IsolateXOther()),
            Theorem("eval_isolate", "Evaluation after isolation",
                "The inverse of Equiv.optionSubtypeNe(w) sends w to none and each other index i to some ⟨i, h⟩ in the option type on Rest(w). Option.elim assigns z on none and uses t on the remaining index. Polynomial.map evaluates the coefficients by the ring homomorphism MvPolynomial.eval(t), and Polynomial.eval then evaluates the outer variable at z.",
                EvalIsolate()),
            Theorem("diff_prime", "Prime coordinate differences",
                "An oriented difference of two distinct variables is prime. Isolate the second variable to turn the factor into a monic linear polynomial.",
                DiffPrime()),
            Theorem("diff_not_dvd_of_edges_ne", "Different unordered pairs give independent factors",
                "Collapse the two coordinates of the divisor to one value and keep the coordinates of the other edge apart. The divisor vanishes but the other factor does not.",
                DiffNotDvdOfEdgesNe()),
            Definition("remainingVertex", "Vertices away from an edge",
                "Each endpoint of a different matching edge survives removal of the distinguished vertex."),
            Definition("remainingProduct", "Product off the distinguished edge",
                "The product uses precisely the edges other than the distinguished edge."),
            Theorem("matching_isolate_left", "Isolation at the first endpoint",
                "Let h prove M(e, true) ≠ M(e, false) by injectivity of M. The second endpoint is indexed by ⟨M(e, true), h⟩ in Rest(M(e, false)). The linear coefficient is the negative of the remaining product. The constant coefficient is the second endpoint variable times that product.",
                MatchingIsolateLeft()),
            Theorem("matching_isolate_right", "Isolation at the second endpoint",
                "Let h prove M(e, false) ≠ M(e, true) by injectivity of M. The first endpoint is indexed by ⟨M(e, false), h⟩ in Rest(M(e, true)). The linear coefficient is the remaining product. The constant coefficient is the negative of the product of the first endpoint variable and the remaining product.",
                MatchingIsolateRight()),
            Theorem("matching_exists_linear", "Linearity in every coordinate",
                "Find the matching edge and endpoint containing the chosen coordinate and apply its ordered isolation formula.",
                MatchingExistsLinear()),
            Theorem("rename_matchingPolynomial", "Transport of matching factors",
                "Renaming the polynomial variables composes the endpoint labeling with the permutation.",
                RenameMatchingPolynomial()),
            Theorem("rename_F_exists_linear", "Linearity after a permutation",
                "The difference of the two transported matching products is at most linear in the chosen coordinate.",
                RenameFExistsLinear()))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula IsolateXSelf() => Seq(
        Forall, Sp, F.Id("V"), Sp, Colon, Sp, Word("Type"), Comma, Sp, OpenBracket, Word("DecidableEq"), Open,
        F.Id("V"), Close, CloseBracket, Comma, Sp, Forall, Sp, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Comma, Sp,
        Word("isolate"), Open, F.Id("w"), Comma, F.Id("X"), Open, F.Id("w"), Close, Close, Sp, Eq, Sp,
        Word("PolynomialX"));

    private static Formula IsolateXOther() => Seq(
        Forall, Sp, F.Id("V"), Sp, Colon, Sp, Word("Type"), Comma, Sp, OpenBracket, Word("DecidableEq"), Open,
        F.Id("V"), Close, CloseBracket, Comma, Sp, Forall, Sp, F.Id("w"), Comma, F.Id("j"), Sp, Colon, Sp,
        F.Id("V"), Comma, Sp, Forall, Sp, F.Id("h"), Sp, Colon, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("w"),
        Comma, Sp, Call("isolate", F.Id("w"), Call("X", F.Id("j"))), Sp, Eq, Sp,
        Apply(Qualified("Polynomial", "C"), Call("X", RemainingIndex(F.Id("j")))));

    private static Formula EvalIsolate() => Seq(
        Forall, Sp, F.Id("V"), Sp, Colon, Sp, Word("Type"), Comma, Sp, OpenBracket, Word("DecidableEq"), Open,
        F.Id("V"), Close, CloseBracket, Comma, Sp, Forall, Sp, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Comma, Sp,
        F.Id("p"), Sp, Colon, Sp, Word("MvPolynomial"), Open, F.Id("V"), Comma, Seq(Mathbb, Grp(F.Id("C"))),
        Close, Comma, Sp, F.Id("t"), Sp, Colon, Sp, Word("Rest"), Open, F.Id("w"), Close, Sp, To, Sp,
        Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp, F.Id("z"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))), Comma,
        Sp, Apply(Qualified("MvPolynomial", "eval"),
            Seq(F.Id("i"), Sp, Mapsto, Sp, Apply(Qualified("Option", "elim"),
                Seq(Open, Apply(Qualified("Equiv", "optionSubtypeNe"), F.Id("w")), Close, Caret, Grp(Minus, D(1)),
                    Open, F.Id("i"), Close), F.Id("z"), F.Id("t"))),
            F.Id("p")), Sp, Eq, Sp,
        Apply(Qualified("Polynomial", "eval"), F.Id("z"),
            Apply(Qualified("Polynomial", "map"),
                Apply(Qualified("MvPolynomial", "eval"), F.Id("t")),
                Call("isolate", F.Id("w"), F.Id("p")))));

    private static Formula DiffPrime() => Seq(
        Forall, Sp, F.Id("V"), Sp, Colon, Sp, Word("Type"), Comma, Sp, Forall, Sp, F.Id("i"), Comma, F.Id("j"),
        Sp, Colon, Sp, F.Id("V"), Comma, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, Implies, Sp, Word("Prime"),
        Open, Word("diff"), Open, F.Id("i"), Comma, F.Id("j"), Close, Close);

    private static Formula DiffNotDvdOfEdgesNe() => Seq(
        Forall, Sp, F.Id("V"), Sp, Colon, Sp, Word("Type"), Comma, Sp, Forall, Sp, F.Id("i"), Comma, F.Id("j"),
        Comma, F.Id("a"), Comma, F.Id("b"), Sp, Colon, Sp, F.Id("V"), Comma, Sp, F.Id("a"), Sp, Neq, Sp,
        F.Id("b"), Sp, Implies, Sp, Neg, Open, Open, F.Id("a"), Eq, F.Id("i"), Sp, Land, Sp, F.Id("b"), Eq,
        F.Id("j"), Close, Sp, Lor, Sp, Open, F.Id("a"), Eq, F.Id("j"), Sp, Land, Sp, F.Id("b"), Eq, F.Id("i"),
        Close, Close, Sp, Implies, Sp, Neg, Open, Word("diff"), Open, F.Id("i"), Comma, F.Id("j"), Close, Sp,
        Mid, Sp, Word("diff"), Open, F.Id("a"), Comma, F.Id("b"), Close, Close);

    private static Formula MatchingIsolateLeft() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("M"),
        Sp, Colon, Sp, Word("Matching"), Open, F.Id("m"), Close, Comma, Sp, F.Id("e"), Sp, Colon, Sp,
        Word("Fin"), Open, F.Id("m"), Close, Comma, Sp, EndpointInequality("true", "false"),
        Word("isolate"), Open, F.Id("M"), Open, F.Id("e"),
        Comma, Word("false"), Close, Comma, Word("matchingPolynomial"), Open, F.Id("M"), Close, Close, Sp, Eq,
        Sp, Qualified("Polynomial", "C"), Open, Minus, Word("remainingProduct"), Open, F.Id("M"), Comma, F.Id("e"),
        Comma, Word("false"), Close, Close, Sp, Cdot, Sp, Qualified("Polynomial", "X"), Sp, Plus, Sp,
        Qualified("Polynomial", "C"), Open, Call("X", RemainingIndex(Call("M", F.Id("e"), Word("true")))),
        Sp, Cdot, Sp, Word("remainingProduct"), Open, F.Id("M"), Comma, F.Id("e"), Comma, Word("false"),
        Close, Close);

    private static Formula MatchingIsolateRight() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("M"),
        Sp, Colon, Sp, Word("Matching"), Open, F.Id("m"), Close, Comma, Sp, F.Id("e"), Sp, Colon, Sp,
        Word("Fin"), Open, F.Id("m"), Close, Comma, Sp, EndpointInequality("false", "true"),
        Word("isolate"), Open, F.Id("M"), Open, F.Id("e"),
        Comma, Word("true"), Close, Comma, Word("matchingPolynomial"), Open, F.Id("M"), Close, Close, Sp, Eq,
        Sp, Qualified("Polynomial", "C"), Open, Word("remainingProduct"), Open, F.Id("M"), Comma, F.Id("e"), Comma,
        Word("true"), Close, Close, Sp, Cdot, Sp, Qualified("Polynomial", "X"), Sp, Plus, Sp,
        Qualified("Polynomial", "C"), Open, Minus, Open,
        Call("X", RemainingIndex(Call("M", F.Id("e"), Word("false")))), Sp, Cdot, Sp,
        Word("remainingProduct"), Open, F.Id("M"), Comma, F.Id("e"), Comma, Word("true"), Close, Close, Close);

    private static Formula RemainingIndex(Formula index) => Seq(Langle, Sp, index, Comma, Sp, F.Id("h"), Sp, Rangle);

    private static Formula EndpointInequality(string remaining, string removed) =>
        Seq(Forall, Sp, F.Id("h"), Sp, Colon, Sp, Call("M", F.Id("e"), Word(remaining)), Sp, Neq, Sp,
            Call("M", F.Id("e"), Word(removed)), Comma, Sp);

    private static Formula Qualified(string owner, string name) => Seq(Word(owner), Dot, Word(name));

    private static Formula Apply(Formula op, params Formula[] operands) =>
        new Formula.Apply(op, [.. operands]);

    private static Formula MatchingExistsLinear() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("M"),
        Sp, Colon, Sp, Word("Matching"), Open, F.Id("m"), Close, Comma, Sp, F.Id("w"), Sp, Colon, Sp,
        Word("Col"), Open, F.Id("m"), Close, Comma, Sp, Exists, Sp, F.Id("A"), Comma, F.Id("B"), Sp, Colon, Sp,
        Word("Coeff"), Open, F.Id("w"), Close, Comma, Sp, Word("isolate"), Open, F.Id("w"), Comma,
        Word("matchingPolynomial"), Open, F.Id("M"), Close, Close, Sp, Eq, Sp, Word("PolynomialC"), Open,
        F.Id("A"), Close, Sp, Cdot, Sp, Word("PolynomialX"), Sp, Plus, Sp, Word("PolynomialC"), Open,
        F.Id("B"), Close);

    private static Formula RenameMatchingPolynomial() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, F.Id("M"),
        Sp, Colon, Sp, Word("Matching"), Open, F.Id("m"), Close, Comma, Sp, Word("rename"), Open, F.Id("s"),
        Comma, Word("matchingPolynomial"), Open, F.Id("M"), Close, Close, Sp, Eq, Sp,
        Word("matchingPolynomial"), Open, F.Id("s"), Sp, Circ, Sp, F.Id("M"), Close);

    private static Formula RenameFExistsLinear() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, F.Id("w"),
        Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, Exists, Sp, F.Id("A"), Comma, F.Id("B"),
        Sp, Colon, Sp, Word("Coeff"), Open, F.Id("w"), Close, Comma, Sp, Word("isolate"), Open, F.Id("w"),
        Comma, Word("rename"), Open, F.Id("s"), Comma, F.Id("F"), Open, F.Id("m"), Close, Close, Close, Sp, Eq,
        Sp, Word("PolynomialC"), Open, F.Id("A"), Close, Sp, Cdot, Sp, Word("PolynomialX"), Sp, Plus, Sp,
        Word("PolynomialC"), Open, F.Id("B"), Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-affine-" + name.ToLowerInvariant().Replace('_', '-');
}
