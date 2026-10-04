using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class BareiRemarkThreeFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.";
    private static readonly LibraryNoteRef Question =
        LibraryNoteRef.Create("D5/L/QuadraticForms/barei2026solvable");
    private static readonly LibraryNoteRef Related =
        LibraryNoteRef.Create("D5/L/QuadraticForms/hu2026idempotent");
    private static readonly LibraryNoteRef Embedding =
        LibraryNoteRef.Create("D5/L/QuadraticForms/costoya2026commutative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-dimensional complex evolution algebra contains a three-dimensional "
            + "idempotent subspace with no nonzero proper idempotent subspace. "
            + "This answers the existence search in Barei's Remark 3.5.",
        H("A three-dimensional minimal idempotent subspace"),
        Blocks(
            Describe.Lean(DescribeId.Create("ambient-space"),
                DeclarationHandle.Create(Prefix + "E"), H("The ambient complex vector space"),
                StatementSource.FromAuthor(AmbientFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ambient vector space has five complex coordinates. "
                    + "The product used in the theorem is bilinear and has an actual natural basis; "
                    + "associativity and a unit are not imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pair-product-square"),
                DeclarationHandle.Create(Prefix + "Square"), H("The square of a subspace"),
                StatementSource.FromAuthor(SquareFormula()), AssessedProvenance.FromLiterature(Question),
                Blocks(Paragraph(Text("The square is the complex linear span of every product "
                    + "of two vectors from the subspace. Idempotence means equality to the subspace. "
                    + "This is a property of subspaces, rather than a restriction to coordinate spans "
                    + "or to idempotent elements."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minimal-idempotent-existence"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Affirmative answer to Remark 3.5"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Question, Related, Embedding),
                Blocks(
                    Paragraph(Text("Choose natural basis e1 through e5. Put u equal to their sum, "
                        + "v equal to e2 minus e3, and w equal to e4 minus e5. The basis squares are "
                        + "4u + 2w, v, -v, v + w, and -v - w; mixed basis products vanish. "
                        + "The injective linear map (a,b,c) to (a,a+b,a-b,a+c,a-c) "
                        + "identifies its range with the span of u,v,w and preserves multiplication.")),
                    Paragraph(Text("In intrinsic coordinates, the products are u squared equal to "
                        + "4u + 2w, uv equal to 2v, uw equal to 2v + 2w, and all products in "
                        + "the plane spanned by v,w equal to zero. These products span the whole "
                        + "three-dimensional space, so its square equals itself.")),
                    Paragraph(Text("Let a multiplication-closed subspace contain x = au + bv + cw "
                        + "with a nonzero. Set s = x squared minus 4ax. Then s = 4acv + 2a squared w "
                        + "and xs - 2as = 4a cubed v. Dividing by nonzero coefficients puts v, "
                        + "then w, then u in the subspace. All remaining subalgebras lie in the "
                        + "square-zero plane. Therefore every nonzero idempotent subspace of "
                        + "the range equals the range. The quantifier includes every complex "
                        + "linear subspace.")),
                    Paragraph(Text("The question is credited to Barei with Muse Spark. Hu and Wen's "
                        + "related counterexamples and Costoya, Fernández Ouaridi and Viruel's "
                        + "evolution-envelope framework are prior literature. The general-dimensional "
                        + "family and its embedding bound are written arguments in the dossier, "
                        + "not additional Lean theorems in this module."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barei-2026-remark-3-5-minimal-idempotent"),
                    ResolutionKind.Proved))), []));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula FinFive() => Call(Named("Fin"), D(5));
    private static Formula Subspaces() => Call(Named("Submodule"), Complexes(), F.Id("E"));
    private static Formula BilinearMaps() => Seq(F.Id("E"), Sp,
        new Formula.Subscript(To, Complexes()), Sp, F.Id("E"), Sp,
        new Formula.Subscript(To, Complexes()), Sp, F.Id("E"));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula SquareOf(Formula subspace) => Call(Named("Square"), Mu, subspace);
    private static Formula Dimension(Formula space) =>
        Call(new Formula.Subscript(Named("finrank"), Complexes()), space);

    private static Formula AmbientFormula() =>
        Disp(Equal(F.Id("E"), Parenthesized(Seq(FinFive(), Sp, To, Sp, Complexes()))));

    private static Formula SquareFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), subspace = F.Id("U");
        Formula products = Seq(OpenBrace, z, Sp, InMacro, Sp, F.Id("E"), Sp, Mid, Sp,
            Some("x", subspace, Some("y", subspace, Equal(Call(Mu, x, y), z))), CloseBrace);
        Formula span = Call(new Formula.Subscript(Named("span"), Complexes()), products);
        return Disp(Seq(Forall, Sp, Mu, Sp, Colon, Sp, BilinearMaps(), Comma, Sp,
            All("U", Subspaces(), Equal(SquareOf(subspace), span))));
    }

    private static Formula ResultFormula()
    {
        Formula basis = F.Id("b"), subspace = F.Id("V"), candidate = F.Id("U");
        Formula naturalBasis = All("i", FinFive(), All("j", FinFive(),
            Implies(new Formula.Relation(F.Id("i"), FormulaRelationOperator.NotEqual, F.Id("j")),
                Equal(Call(Mu, Call(basis, F.Id("i")), Call(basis, F.Id("j"))), D(0)))));
        Formula minimality = All("U", Subspaces(),
            Implies(Seq(candidate, Sp, Leq, Sp, subspace),
                Implies(new Formula.Relation(candidate, FormulaRelationOperator.NotEqual,
                    new Formula.SetLiteral([D(0)])),
                    Implies(Equal(SquareOf(candidate), candidate), Equal(candidate, subspace)))));
        Formula conditions = And(Equal(Dimension(F.Id("E")), D(5)),
            And(naturalBasis, And(Equal(Dimension(subspace), D(3)),
                And(Equal(SquareOf(subspace), subspace), minimality))));
        Formula basisType = Call(new Formula.Subscript(Named("Basis"), Complexes()), FinFive(), F.Id("E"));
        return Disp(Seq(Exists, Sp, Mu, Sp, Colon, Sp, BilinearMaps(), Comma, Sp,
            Some("b", basisType, Some("V", Subspaces(), conditions))));
    }
}
