using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class SraSymmetricAlphaPermanentRefutationDocument : IScribeDocumentDefinition
{

    private const string Prefix = "D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/sra2026koteljanskii");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetry of an inverse M matrix does not force log-supermodularity of every positive-order alpha-permanent.",
        H("Sra: symmetric alpha-permanent assertion"), Blocks(
            Node("symmetrizable", "Symmetrizable", SymmetrizableFormula(),
                "Source, p. 1: “We prove (1.1) for inverse M-matrices that are symmetric after a positive diagonal similarity, which we call symmetrizable, and show that (1.1) can fail without this hypothesis.” The positive function delta gives that diagonal similarity.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("alpha", "alphaPermanent", AlphaFormula(),
                "Source, p. 5, equation (3.1): “For α>0, the α-permanent of a matrix H indexed by S is” the permutation sum, “where 𝔖(S) is the group of permutations of S and c(π) is the number of cycles of π; the ordinary permanent is α=1.” The exponent adds nontrivial cycles and fixed points, including one-cycles; the empty permutation gives one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("principal", "principalAlphaPermanent", PrincipalFormula(),
                "Source, p. 1: “For an n×n matrix A and S⊆[n], write A_S=A[S,S] for the principal submatrix with row and column set S, and set det(A_∅)=per(A_∅)=1.” Here Matrix.submatrix uses the subtype S and val denotes its underlying Fin n index; the same restriction is used for the alpha-permanent.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", Disp(IffTo(F.Id("claim"), ClaimBody())),
                "Source, p. 6, §4(b): “For symmetrizable inverse M-matrices and α∉{½,1}, decide whether S↦per_α(A_S) is log-supermodular.” Alpha is positive as in equation (3.1). The formula is the universal affirmative assertion, with both distinguished positive orders excluded. Fin n index i represents source index i+1, and S,T range over finite subsets of those indices.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "The symmetric matrix with rows (7,2,1,2), (2,7,2,1), (1,2,7,2), (2,1,2,7) is entrywise positive and inverse M. For S={0,1,2} and T={0,2,3}, the union-intersection product minus the S,T product equals alpha²(alpha+1)(2401alpha²+1617alpha−16), which is negative throughout 0<alpha≤1/200. Taking alpha=1/200 refutes the assertion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))), []));
    private static DocumentBlock Node(string id, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula SymmetrizableFormula() =>
        Disp(All("n", N(), All("A", MatN(), IffTo(Call("Symmetrizable", F.Id("A")), Some("delta", new Formula.TypeArrow(FinN(), R()), And(All("i", FinN(), LtTo(D(0), App(F.Id("delta"), F.Id("i")))), App(Q("Matrix", "IsSymm"), TimesOf(TimesOf(App(Q("Matrix", "diagonal"), F.Id("delta")), F.Id("A")), App(Q("Matrix", "diagonal"), LambdaOf("i", FinN(), PowOf(App(F.Id("delta"), F.Id("i")), Seq(Minus, D(1)))))))))))));
    private static Formula Instances(Formula body) => Seq(OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp, OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Sp, body);
    private static Formula AlphaFormula() =>
        Disp(All("I", Seq(F.Id("Type"), Star), Instances(
            All("alpha", R(), All("H", Call("Matrix", F.Id("I"), F.Id("I"), R()),
                EqTo(Call("alphaPermanent", F.Id("alpha"), F.Id("H")),
                    SumOver("pi", App(Q("Equiv", "Perm"), F.Id("I")),
                        TimesOf(PowOf(F.Id("alpha"), CycleExponent()),
                            ProductOver("i", F.Id("I"), App(F.Id("H"), F.Id("i"), App(F.Id("pi"), F.Id("i"))))))))))));
    private static Formula CycleExponent() =>
        Add(App(Q("Multiset", "card"), Call("cycleType", F.Id("pi"))),
            App(Q("Finset", "card"), App(Q("Finset", "filter"),
                LambdaOf("i", F.Id("I"), EqTo(App(F.Id("pi"), F.Id("i")), F.Id("i"))), F.Id("univ"))));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body)));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Prod, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body)));
    private static Formula PrincipalFormula() =>
        Disp(All("n", N(), All("alpha", R(), All("A", MatN(), All("S", Finsets(), EqTo(Call("principalAlphaPermanent", F.Id("alpha"), F.Id("A"), F.Id("S")), Call("alphaPermanent", F.Id("alpha"), App(Q("Matrix", "submatrix"), F.Id("A"), LambdaOf("i", F.Id("S"), Call("val", F.Id("i"))), LambdaOf("j", F.Id("S"), Call("val", F.Id("j")))))))))));
    private static Formula ClaimBody() =>
        All("n", N(), ImpliesTo(LtTo(D(0), F.Id("n")), All("A", MatN(), ImpliesTo(App(Q("SraReciprocalPermanentLorentzianRefutation", "InverseMMatrix"), F.Id("A")), ImpliesTo(Call("Symmetrizable", F.Id("A")), All("alpha", R(), ImpliesTo(LtTo(D(0), F.Id("alpha")), ImpliesTo(NeTo(F.Id("alpha"), new Formula.Fraction(D(1), D(2))), ImpliesTo(NeTo(F.Id("alpha"), D(1)), All("S", Finsets(), All("T", Finsets(), LeTo(TimesOf(Call("principalAlphaPermanent", F.Id("alpha"), F.Id("A"), F.Id("S")), Call("principalAlphaPermanent", F.Id("alpha"), F.Id("A"), F.Id("T"))), TimesOf(Call("principalAlphaPermanent", F.Id("alpha"), F.Id("A"), App(Q("Finset", "union"), F.Id("S"), F.Id("T"))), Call("principalAlphaPermanent", F.Id("alpha"), F.Id("A"), App(Q("Finset", "inter"), F.Id("S"), F.Id("T"))))))))))))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula NeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula TimesOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula PowOf(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula LambdaOf(string name, Formula domain, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, domain)), Sp, Mapsto, Sp, body);
    private static Formula R() => Seq(Mathbb, Sp, Grp(F.Id("R")));
    private static Formula N() => Seq(Mathbb, Sp, Grp(F.Id("N")));
    private static Formula FinN() => Call("Fin", F.Id("n"));
    private static Formula MatN() => Call("Matrix", FinN(), FinN(), R());
    private static Formula Finsets() => Call("Finset", FinN());
}
