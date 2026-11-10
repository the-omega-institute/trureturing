using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class SemisimpleDerivationClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semisimple derivation algebras are sums of orthogonal algebras.",
        H("Semisimple derivation algebras are sums of orthogonal algebras"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("radical-transfer-equivalence"),
                DeclarationHandle.Create(Prefix + "trivialRadical_of_equiv"),
                H("Transfer of trivial radical through a Lie equivalence"),
                StatementSource.FromAuthor(Disp(TransferFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary Lie algebras L and N over a field, a Lie equivalence L to N transfers trivial actual solvable radical from L to N. This is the original canonical proof made public for the actual orthogonal dimension-four split; the existing semisimple classification and all its hypotheses retain their meanings."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonalzero"),
                DeclarationHandle.Create(Prefix + "diagonal_zero"),
                H("Zero diagonal coefficients"),
                StatementSource.FromAuthor(Disp(OrthogonalParameters(
                    All(X("i"), X("n"), Eq(Call("val", X("A"), X("i"), X("i")), D(0)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every diagonal coefficient of an orthogonal Lie algebra matrix vanishes in characteristic zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coefficientskew"),
                DeclarationHandle.Create(Prefix + "coefficient_skew"),
                H("Skew transpose coefficients"),
                StatementSource.FromAuthor(Disp(OrthogonalParameters(
                    All(X("i"), X("n"), All(X("j"), X("n"),
                        Eq(Call("val", X("A"), X("j"), X("i")),
                            Seq(Minus, Call("val", X("A"), X("i"), X("j"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Transposing the indices negates each coefficient of an orthogonal Lie algebra matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("claim"),
                StatementSource.FromAuthor(Disp(Eq(Name("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 5 (Semisimple derivation algebras), p. 28: “Let k be algebraically closed of characteristic 0. If Der(A) is semisimple for a finite-dimensional evolution algebra A, then Der(A) ≅ ⊕ᵢ so_{mᵢ} with mᵢ ≥ 3.” The field k and vector space V are arbitrary; μ is the bilinear product, and r = 0 permits the zero Lie algebra."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("result"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The annihilator obstruction removes zero natural squares. The block decomposition identifies all derivations with independent orthogonal pointwise stabilizers. Their radical quotients give standard orthogonal algebras. Dimensions zero and one contribute zero, and dimension two is excluded by its nonzero abelian algebra. The remaining factors have dimension at least three."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kaygorodov-martin-gonzalez-viruel-2026-evolution-algebra-derivations-conjecture-5"),
                    ResolutionKind.Proved)))));

    private static Formula TransferFormula() => All(X("k"), Type,
        Instance(Call("Field", X("k")),
        All(X("L"), Type, Instance(Call("LieRing", X("L")),
        Instance(Call("LieAlgebra", X("k"), X("L")),
        All(X("N"), Type, Instance(Call("LieRing", X("N")),
        Instance(Call("LieAlgebra", X("k"), X("N")),
        Instance(Apply(Qualified("LieAlgebra", "HasTrivialRadical"), X("k"), X("L")),
        All(X("e"), LieEquivalence(X("L"), X("N")),
            Apply(Qualified("LieAlgebra", "HasTrivialRadical"), X("k"), X("N"))))))))))));
    private static Formula OrthogonalParameters(Formula body) => All(X("k"), Type,
        Instance(Call("Field", X("k")), Instance(Call("CharZero", X("k")),
        All(X("n"), Type, Instance(Call("Fintype", X("n")), Instance(Call("DecidableEq", X("n")),
        All(X("A"), So(X("n")), body)))))));
    private static Formula Parenthesized(Formula content) =>Seq(Open, content, Close);
    private static Formula X(string name) =>F.Id(name);
    private static Formula Name(string name) =>Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) =>Seq(Name(owner), Dot, Name(name));
    private static Formula Apply(Formula f, params Formula[] args) =>new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>Apply(Name(name), args);
    private static Formula All(Formula x, Formula type, Formula body) =>Seq(Forall, Sp, Parenthesized(Seq(x, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula x, Formula type, Formula body) =>Seq(Exists, Sp, Parenthesized(Seq(x, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Fn(Formula x, Formula body) =>Parenthesized(Seq(Name("fun"), Sp, x, Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) =>Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula LMap(Formula a, Formula b) =>Call("LinearMap", X("k"), a, b);
    private static Formula Type =>Name("Type");
    private static Formula Nat =>Seq(Mathbb, Grp(X("N")));
    private static Formula Product =>LMap(X("V"), LMap(X("V"), X("V")));
    private static Formula Der =>Call("derivations", Mu);
    private static Formula So(Formula n) =>Apply(Seq(Name("LieAlgebra"), Dot, Name("Orthogonal"), Dot, Name("so")), n, X("k"));
    private static Formula LieEquivalence(Formula a, Formula b) =>Call("LieEquiv", X("k"), a, b);
    private static Formula Sum(Formula i, Formula type, Formula body) =>Call("DirectSum", type, Fn(i, body));
    private static Formula Nonempty(Formula t) =>Call("Nonempty", t);
    private static Formula ClaimBody() =>All(X("k"), Type,
        Instance(Call("Field", X("k")), Instance(Call("IsAlgClosed", X("k")), Instance(Call("CharZero", X("k")),
        All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", X("k"), X("V")),
        Instance(Call("FiniteDimensional", X("k"), X("V")), All(Mu, Product,
        Imp(Call("IsEvolutionAlgebra", Mu), Imp(Apply(Qualified("LieAlgebra", "IsSemisimple"), X("k"), Der),
        Some(X("r"), Nat, Some(X("m"), Arrow(Call("Fin", X("r")), Nat),
        And(All(X("i"), Call("Fin", X("r")), new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, Apply(X("m"), X("i")))),
        Nonempty(LieEquivalence(Der, Sum(X("i"), Call("Fin", X("r")), So(Call("Fin", Apply(X("m"), X("i")))))))))))))))))))));
}
