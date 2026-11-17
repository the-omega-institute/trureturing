using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class PlanarDiagramAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal planar diagram algebra", H("The literal planar diagram algebra"), Blocks(
            Paragraph(Text("The coefficient ring R is commutative. Diagram n contains the " +
                "literal boundary matchings with a noncrossing representative; " +
                "there is no quotient on pairings. TL(R,n) is the free " +
                "coefficient module on this set. Its multiplication is the " +
                "bilinear extension of path concatenation, with every internal " +
                "loop assigned zero.")),

            Node("Diagram", All("n", Nat(), Eq(Call("Diagram", X("n")),
                Call("Subtype", Fn("d", Call("Matching", Call("Boundary", X("n"))),
                    Ex("M", Call("CupCapBridgeProposal.NCMatching", Mul(D(2), X("n"))),
                        Eq(Call("toMatching", X("M")), X("d"))))))),
                "This is the full zero-fugacity Temperley-Lieb diagram basis.", literature: true),
            Node("TL", Scope(Eq(TL(), Call("MonoidAlgebra", X("R"), Call("Diagram", X("n"))))),
                "MonoidAlgebra supplies the finite-support coefficient carrier." +
                " No multiplication is assumed on Diagram n.",
                literature: true),
            Node("additiveWithOne", Scope(Eq(Call("additiveWithOne", X("R"), X("n")),
                Record(Field("toAddCommGroup", Typed(N("inferInstance"), Call("AddCommGroup",
                TL()))),
                    Field("one", Call("MonoidAlgebra.single", Call("identity", X("n")), D(1)))))),
                "The existing additive commutative group is extended by the " +
                "single identity diagram with coefficient one. Here identity n " +
                "is Subtype.mk (identityMatching n) (identity_planar n)."),
            Node("ring", Scope(Eq(Call("ring", X("R"), X("n")), Record(
                Field("toAddCommGroup", Call("AddCommGroupWithOne.toAddCommGroup",
                    N("additiveWithOne"))),
                Field("toAddGroupWithOne", Call("AddCommGroupWithOne.toAddGroupWithOne",
                    N("additiveWithOne"))), Field("mul_assoc", N("mul_assoc'")),
                Field("one_mul", N("one_mul'")), Field("mul_one", N("mul_one'")),
                Field("left_distrib", N("mul_add'")), Field("right_distrib", N("add_mul'")),
                Field("zero_mul", N("zero_mul'")), Field("mul_zero", N("mul_zero'"))))),
                "The additive projections expand the inherited additiveWithOne entry. " +
                "The remaining entries are the literal Ring record fields. The existing " +
                "multiplication is instMulTL; the loop cocycle gives basis " +
                "associativity and linear extension gives the ring laws."),
            Node("algebra", Scope(Eq(Call("algebra", X("R"), X("n")),
                Call("Algebra.ofModule", N("smul_mul'"), N("mul_smul'")))),
                "The two named scalar compatibility proofs define the algebra " +
                "structure from the existing R-module."),
            Node("single_mul_single", Scope(All("a", Call("Diagram", X("n")),
                All("b", Call("Diagram", X("n")), All("r", X("R"), All("s", X("R"),
                    Eq(Mul(Typed(Call("MonoidAlgebra.single", X("a"), X("r")), TL()),
                        Call("MonoidAlgebra.single", X("b"), X("s"))),
                        If(Eq(Call("internalLoopCount", SubVal(X("a")), SubVal(X("b"))), D(0)),
                            Call("MonoidAlgebra.single", Call("concat", X("a"), X("b")),
                                Mul(X("r"), X("s"))), D(0)))))))),
                "The actual private concat has underlying matching composite " +
                "(Subtype.val a) (Subtype.val b); composite_planar supplies the" +
                " subtype proof. No extra operation on diagrams is introduced.",
                DescribeRole.Theorem),
            Node("generator", Scope(All("i", Fin(Call("Nat.sub", X("n"), D(1))),
                Eq(Typed(Call("generator", X("i")), TL()), Call("MonoidAlgebra.single",
                    Call("Subtype.mk", Call("cupcapMatching", Val(X("i")), OmegaProof()),
                        Call("cupcap_planar", X("n"), Val(X("i")), OmegaProof())), D(1))))),
                "The paper labels this cup-cap by Fin.val i+1; Lean uses the " +
                "zero-based finite index i.",
                literature: true),
            Node("h", Scope(Eq(Call("h", X("R"), X("n")),
                Negate(SumOver("i", Fin(Call("Nat.sub", X("n"), D(1))),
                    Typed(Call("generator", X("i")), TL()))))),
                "Equation (4.69) is the negative sum of the n-1 open-boundary " +
                "generators. Fin(n-1) is empty for n=0 and n=1.",
                literature: true),
            Node("instMulTL", Scope(Eq(Call("instMulTL", X("R"), X("n")),
                Call("Mul.mk", Fn("a", TL(), Fn("b", TL(), Call("bilinear", X("a"), X("b"))))))),
                "The literal private bilinear is the composition of two " +
                "Finsupp.lift maps with " +
                "MonoidAlgebra.coeffLinearEquiv.toLinearMap. Its basisProduct " +
                "is MonoidAlgebra.single (concat a b) 1 when internalLoopCount " +
                "a.val b.val=0, and zero otherwise.",
                literature: true),
            Node("instOneTL", Scope(Eq(Call("instOneTL", X("R"), X("n")),
                Call("One.mk", Call("MonoidAlgebra.single", Call("identity", X("n")), D(1))))),
                "The literal private identity is Subtype.mk (identityMatching " +
                "n) (identity_planar n).",
                literature: true))));

    private static Formula Scope(Formula body) => Ring(All("n", Nat(), body));
    private static Formula TL() => Call("TL", X("R"), X("n"));


    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/poncini2023planar");
    private static Formula X(string name) => F.Id(name);

    private static Formula N(string name) => Q(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((s, i) =>
        i == 0 ? new[] { NamePart(s) } : new[] { Dot, NamePart(s) }).ToArray());
    private static Formula NamePart(string name)
    {
        bool prime = name.EndsWith('\'');
        var words = name.Replace("'", "").Split('_');
        Formula result = F.Id(words[^1]);
        for (int i = words.Length - 2; i >= 0; --i)
            result = Seq(F.Id(words[i]), Underscore, Grp(result));
        return prime ? Seq(Operatorname, Grp(result), Apos) : Seq(Operatorname, Grp(result));
    }

    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula D(long n) => n < 0 ? Negate(D(-n)) : Num(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) => Typed(X(name), type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Bound(name, type), Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula If(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Nat() => N("Nat");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula SubVal(Formula x) => Call("Subtype.val", x);
    private static Formula OmegaProof() => Seq(N("by"), Sp, N("omega"));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Call("Finset.sum", Call("Finset.univ"), Fn(name, type, body));
    private static Formula Ring(Formula body) => All("R", N("Type"),
        Seq(OpenBracket, Call("CommRing", X("R")), CloseBracket, Sp, body));
    private static Formula Field(string name, Formula value) =>
        Seq(Q(name), Sp, Colon, F.Eq, Sp, value);
    private static Formula Record(params Formula[] fields) => Seq(OpenBrace, Sp,
        Seq(fields.SelectMany((f, i) => i == 0 ? new[] { f } :
            new[] { Comma, Sp, f }).ToArray()), Sp, CloseBrace);
    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, bool literature = false,
        bool acknowledgeSource = false) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) :
                acknowledgeSource ? AssessedProvenance.FromRepo(Source) :
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

}
