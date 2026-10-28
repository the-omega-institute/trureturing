using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class HilbertNaturalBasisNonuniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.";
    private static readonly LibraryNoteRef Survey = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");
    private static readonly LibraryNoteRef Hilbert = LibraryNoteRef.Create("D5/L/QuadraticForms/vidalcadavidrodriguez2020hilbert");
    private static readonly LibraryNoteRef Table = LibraryNoteRef.Create("D5/L/QuadraticForms/cabrera2025solenoids");
    private static readonly LibraryNoteRef Rotation = LibraryNoteRef.Create("D5/L/QuadraticForms/cadavidrodriguezvidal2023nilpotency");

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [..args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(X("fun"), Sp, Open, X(name), Colon, type, Close, Sp, Mapsto, Sp, body);
    private static Formula C => X("Complex");
    private static Formula R => X("Real");
    private static Formula P => X("PNat");
    private static Formula HSpace => Call("lp", App(Q("Function", "const"), P, C), D(2));
    private static Formula A => X("A");
    private static Formula M => X("m");
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Ei(Formula i) => App(X("e"), i);
    private static Formula Mi(Formula x, Formula y) => App(X("mu"), x, y);
    private static Formula Bilinear(Formula k, Formula a) => Call("LinearMap", k, a, Call("LinearMap", k, a, a));
    private static Formula Basis(Formula k, Formula a) => Call("HilbertBasis", P, k, a);
    private static Formula PositiveBound => All("v", A, Some("M", R,
        And(Rel(D(0), FormulaRelationOperator.LessThan, X("M")), All("w", A,
            Rel(Norm(App(M, X("v"), X("w"))), FormulaRelationOperator.LessThanOrEqual,
                Mul(X("M"), Norm(X("w"))))))));
    private static Formula Natural(Formula basis) => All("i", P, All("j", P,
        Imp(Rel(X("i"), FormulaRelationOperator.NotEqual, X("j")),
            Equal(App(M, App(basis, X("i")), App(basis, X("j"))), D(0)))));
    private static Formula Square(Formula k) => App(Q("Submodule", "span"), k,
        Seq(OpenBrace, X("z"), Colon, A, Sp, Mid, Sp,
            Some("x", A, Some("y", A, Equal(App(M, X("x"), X("y")), X("z")))), CloseBrace));
    private static Formula DenseSquare(Formula k) =>
        Equal(App(Q("Submodule", "topologicalClosure"), Square(k)), Q("Top", "top"));
    private static Formula Identification(Formula k) =>
        Some("sigma", App(Q("Equiv", "Perm"), P), Some("c", Seq(P, Sp, To, Sp, k),
            And(All("i", P, Equal(Norm(App(X("c"), X("i"))), D(1))),
                All("i", P, Equal(App(X("b"), X("i")),
                    Smul(App(X("c"), X("i")), App(X("a"), App(X("sigma"), X("i")))))))));
    private static Formula Full(Formula k)
    {
        var body = Identification(k);
        body = Imp(DenseSquare(k), body);
        body = Imp(Natural(X("b")), body);
        body = Imp(Natural(X("a")), body);
        body = Imp(PositiveBound, body);
        body = All("b", Basis(k, A), body);
        body = All("a", Basis(k, A), body);
        body = All("m", Bilinear(k, A), body);
        return All("A", X("Type"), Seq(
            OpenBracket, Call("NormedAddCommGroup", A), CloseBracket, Sp,
            OpenBracket, Call("InnerProductSpace", k, A), CloseBracket, Sp,
            OpenBracket, Call("CompleteSpace", A), CloseBracket, Sp,
            OpenBracket, Call("SeparableSpace", A), CloseBracket, Comma, Sp, body));
    }
    private static Formula WholeClaim => And(Full(R), Full(C));
    private static DocumentBlock.Describe Desc(string name, string title, Formula formula, string text,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(text))), role,
            openProblemResolutionClaim: resolution);

    public DocumentDefinition Create()
    {
        var i = X("i");
        var first = Add(Smul(new Formula.Fraction(D(3), D(5)), Ei(D(1))),
            Smul(new Formula.Fraction(D(4), D(5)), Ei(D(2))));
        var second = Add(Smul(new Formula.Fraction(Seq(Minus, D(4)), D(5)), Ei(D(1))),
            Smul(new Formula.Fraction(D(3), D(5)), Ei(D(2))));
        var predecessor = Call("ite", Equal(i, D(1)), D(1), Seq(i, Minus, D(1)));
        var sum = Call("tsum", Lam("i", P,
            Smul(Mul(App(X("x"), i), App(X("y"), i)), Ei(predecessor))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Dense algebraic square does not force uniqueness of a complete natural orthonormal basis of a Hilbert evolution algebra.",
            H("A dense-square Hilbert algebra with two different natural orthonormal bases"), Blocks(
                Paragraph(Text("Question 46 in section 2.2.8 of Kaygorodov, Martin Gonzalez and Viruel asks: If the square of a Hilbert evolution algebra is dense, is its natural orthonormal basis unique up to permutation and unimodular scalars? "
                    + "The square means the algebraic span of all products; density and completeness use the Hilbert norm. Definition 2.2 of Vidal, Cadavid and Rodriguez permits real or complex scalars and requires bounded left multiplication for every fixed vector. "
                    + "The two scalar cases are conjoined in claim. Its complex branch alone fails. The separate questions about derivations, automorphisms and spectral theory are outside this assertion.")),
                Paragraph(Text("The witness space is the complex square-summable sequence space lp on all positive integers at exponent two, with its standard norm and inner product. It is complete and separable. The standard orthonormal family has closed linear span equal to the whole space; no algebraic Hamel basis is used.")),
                Desc("e", "The standard complete orthonormal basis",
                    Equal(X("e"), App(Q("HilbertBasis", "ofRepr"), App(Q("LinearIsometryEquiv", "refl"), C, HSpace))),
                    "The identity isometric representation of the sequence space supplies e. Each e(i) is the sequence with coordinate one at i and zero elsewhere.",
                    AssessedProvenance.FromLiterature(Hilbert)),
                Desc("mu", "A continuous complex-bilinear multiplication",
                    And(Rel(X("mu"), FormulaRelationOperator.MemberOf,
                            Call("ContinuousLinearMap", C, HSpace, Call("ContinuousLinearMap", C, HSpace, HSpace))),
                        All("x", HSpace, All("y", HSpace, Equal(Mi(X("x"), X("y")), sum)))),
                    "The series converges in the sequence space by the lp.dualPairing construction from uniformly bounded coordinate bilinear maps and the two-two Holder pairing. Scalar multiplication is complex-linear in both inputs: the coefficient is x(i)y(i), without conjugation. "
                    + "The table is e(1)^2=e(2)^2=e(1) and e(i+1)^2=e(i), with every mixed standard-basis product zero. This table is Example 3.7 of Solenoids in automorphism groups of evolution algebras. "
                    + "For each v the positive number norm(mu(v))+1 bounds left multiplication on every w. Joint continuity of this particular product is stronger than the left-multiplication requirement.",
                    AssessedProvenance.FromRepo(Table, Hilbert)),
                Desc("f", "The second complete orthonormal basis",
                    And(Rel(X("f"), FormulaRelationOperator.MemberOf, Basis(C, HSpace)),
                        All("i", P, Equal(App(X("f"), i), Call("ite", Equal(i, D(1)), first,
                            Call("ite", Equal(i, D(2)), second, Ei(i)))))),
                    "Only the first two basis vectors change. The real coefficients 3/5 and 4/5 satisfy 9/25+16/25=1, so this block is unitary over the complex scalars. "
                    + "Its inverse gives e(1)=(3/5)f(1)-(4/5)f(2) and e(2)=(4/5)f(1)+(3/5)f(2); all other vectors agree. Thus the closed span is the whole sequence space. "
                    + "Since e(1)^2=e(2)^2, the two mixed terms cancel and f is natural for the same multiplication. The equal-square rotation method occurs in Examples 3.6-3.7 of Hilbert evolution algebras, weighted digraphs, and nilpotency.",
                    AssessedProvenance.FromRepo(Rotation)),
                Desc("uniqueness", "The scalar-specific universal assertion",
                    All("k", X("Type"), Seq(OpenBracket, Call("RCLike", X("k")), CloseBracket,
                        Comma, Sp, Iff(Call("uniqueness", X("k")), Full(X("k"))))),
                    "All complete separable Hilbert spaces over k, all bilinear products with the stated positive left bounds, and both complete natural orthonormal bases are quantified. A dense square is the only extra premise. "
                    + "The conclusion allows every permutation of the positive integers and every scalar family of norm one. The bracketed assumptions denote the corresponding chosen Lean structures or instances. RCLike supplies the real and complex specializations used in claim.",
                    AssessedProvenance.FromLiterature(Survey)),
                Desc("claim", "The entire real-or-complex source assertion",
                    Iff(X("claim"), WholeClaim),
                    "Question 46, page 26: If the square of a Hilbert evolution algebra is dense, is its natural orthonormal basis unique up to permutation and unimodular scalars? "
                    + "The real universal assertion and the complex universal assertion are both required. Their conjunction faithfully states the first interrogative under the complete Hilbert-space convention. The complex assertion alone is a consequence of this conjunction; they are not asserted equivalent.",
                    AssessedProvenance.FromLiterature(Survey)),
                Desc("result", "Refutation by the complex Hilbert example", new Formula.Not(WholeClaim),
                    "Apply the complex universal assertion to the sequence space, mu, e and f. Every standard vector e(i) is the product mu(e(i+1),e(i+1)), so the algebraic product span contains the standard span and its norm closure is the whole space. "
                    + "Both bases are complete, orthonormal and natural. However, f(1) has two nonzero standard coordinates and differs from c times e(j) for every positive j and every complex c. "
                    + "Any proposed permutation and unimodular scalar family would give such an equality at index one. This contradiction refutes the complex assertion and hence the real-or-complex conjunction. The equal-square pair is the failure mechanism: dense square does not forbid two equal nonzero basis squares.",
                    AssessedProvenance.FromRepo(Survey, Table, Hilbert, Rotation), DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("kaygorodov-martin-gonzalez-viruel-2026-hilbert-natural-basis-uniqueness"),
                        ResolutionKind.Refuted))), []));
    }
}
