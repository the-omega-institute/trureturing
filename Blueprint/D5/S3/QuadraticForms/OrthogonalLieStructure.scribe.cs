using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class OrthogonalLieStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/OrthogonalLieStructure.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical structure of actual standard orthogonal Lie algebras.",
        H("Standard orthogonal Lie algebras"),
        Blocks(
            Entry("isSimple_of_card_ne_four", "Actual simplicity outside dimension four",
                Context(All(X("n"), Type, Instance(Call("Fintype", X("n")),
                    Instance(Call("DecidableEq", X("n")),
                    Imp(Le(D(3), Call("Fintype.card", X("n"))),
                    Imp(Ne(Call("Fintype.card", X("n")), D(4)), Call("LieAlgebra.IsSimple", X("k"), So(X("n"))))))))),
                "Over every characteristic-zero field, actual so_n is nonabelian simple when the finite index type has cardinality three or at least five. Double rotation brackets give coordinate projectors. Two projectors isolate a nonzero rotation in size three; four projectors isolate it when five distinct indices are available. Brackets of that rotation generate all rotations and hence the whole algebra. This proves the ideal dichotomy for actual matrix ideals. Size four is treated by the separate actual split equivalence.", DescribeRole.Theorem),
            Entry("hasTrivialRadical_of_card_ne_four", "Trivial radical outside dimension four",
                Context(All(X("n"), Type, Instance(Call("Fintype", X("n")),
                    Instance(Call("DecidableEq", X("n")),
                    Imp(Le(D(3), Call("Fintype.card", X("n"))),
                    Imp(Ne(Call("Fintype.card", X("n")), D(4)), RadicalFree(So(X("n"))))))))),
                "For every characteristic-zero field and every finite decidable index type of cardinality at least three and different from four, the actual standard orthogonal matrix Lie algebra has zero solvable radical. The proved actual simplicity supplies trivial solvable radical through mathlib’s standard instance. This is classical structure, not a novelty claim.", DescribeRole.Theorem),
            Entry("soFourEquiv", "The actual dimension-four split",
                Context(Seq(X("soFourEquiv"), Sp, Colon, Sp,
                    Call("LieEquiv", X("k"), So(Call("Fin", D(4))),
                        Call("Prod", So(Call("Fin", D(3))), So(Call("Fin", D(3))))))),
                "For every characteristic-zero field, this explicit Lie equivalence maps a skew four-by-four matrix with upper entries (a,b,c,d,e,f) to skew three-by-three matrices with upper triples (a+f,b-e,c+d) and (a-f,b+e,d-c). The inverse recovers a=(pL+pR)/2, b=(qL+qR)/2, c=(rL-rR)/2, d=(rL+rR)/2, e=(qR-qL)/2 and f=(pL-pR)/2. The linear inverse and bracket identities are proved for the actual matrices. No algebraic-closedness hypothesis is used.", DescribeRole.Definition),
            Entry("so_four_hasTrivialRadical", "Trivial radical in dimension four",
                Context(RadicalFree(So(Call("Fin", D(4))))),
                "The explicit split and the radical-free dimension-three factors imply zero actual solvable radical in dimension four.", DescribeRole.Theorem),
            Entry("hasTrivialRadical", "All dimensions at least three",
                Context(All(X("m"), Call("Nat"),
                    Imp(Le(D(3), X("m")), RadicalFree(So(Call("Fin", X("m"))))))),
                "For every characteristic-zero field and every integer m at least three, so_m has zero actual solvable radical, including m=4. This theorem alone does not prove simplicity, classify evolution derivations, identify their radical quotient, or exclude the genuine Serre G2 algebra. Those remain separate obligations of the Ma-then-Zhang credited KMV application.", DescribeRole.Theorem))));
    private static DocumentBlock.Describe Entry(string name, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula X(string s) => F.Id(s);
    private static Formula Type => Call("Type");
    private static Formula Qualified(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new Formula[] { Seq(Operatorname, Grp(X(part))) } :
            new Formula[] { Dot, Seq(Operatorname, Grp(X(part))) }).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Qualified(s), [.. xs]);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Forall, Sp, Open, x, Sp, Colon, Sp, t, Close, Comma, Sp, Open, b, Close);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula So(Formula n) => Call("LieAlgebra.Orthogonal.so", n, X("k"));
    private static Formula RadicalFree(Formula l) => Call("LieAlgebra.HasTrivialRadical", X("k"), l);
    private static Formula Context(Formula b) => All(X("k"), Type, Instance(Call("Field", X("k")), Instance(Call("CharZero", X("k")), b)));
}
