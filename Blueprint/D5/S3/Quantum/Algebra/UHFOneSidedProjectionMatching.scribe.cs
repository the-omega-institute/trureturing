using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class UHFOneSidedProjectionMatchingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual completed-algebra projections localize in finite matrix stages and admit one-sided matching.",
        H("Intrinsic localization and one-sided projection matching"), Blocks(
            Paragraph(Text("FullMatrixModel C consists of natural stage sizes, injective unital complex star-algebra maps from the corresponding full matrix algebras into C, increasing ranges, and a norm-dense union of those ranges. Matrix norms are the L2 operator norms. Localization and matching are conclusions, not fields of the model.")),
            Paragraph(Text("The shared coordinate-projection lemma proj_single states that the diagonal matrix unit with coefficient one is a self-adjoint projection in every natural dimension. Both the finite-stage matching proof and the projection-span argument for the sequential Born-rule dichotomy use this same lemma. It has no state, channel, or Born-rule premise.")),
            Describe.Lean(DescribeId.Create("completed-projection-finite-stage-localization"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching.localize_projection"),
                H("Exact finite-stage localization"), StatementSource.FromAuthor(Localization()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/blackadar2006operatoralgebras")),
                Blocks(Paragraph(Text("Symmetrize a dense finite-stage approximant. Its idempotence defect bounds each eigenvalue, so rounding at one half gives a finite-stage projection close in operator norm. The intrinsic polar decomposition of the near-projection intertwiner supplies a unitary in C. Zero projections are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("completed-projections-one-sided-matching"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching.one_sided_projection_matching"),
                H("One-sided complete partition with one common initial projection"),
                StatementSource.FromAuthor(Matching()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/blackadar2006operatoralgebras")),
                Blocks(Paragraph(Text("Apply proved localization separately to both arbitrary projections. In a common later actual matrix stage, split the first projection into rank-one pieces and choose one rank-one subprojection of the second. Matrix units give the partial isometries. Transport all pieces and that one common initial projection back into C. The identities mv = vm = m express projection subordination in the intrinsic spectral order.")),
                    Paragraph(Text("The finite family is indexed by the nonempty finite set s; values of l and w outside s carry no requirement. No growth, parity, whole-rank equality, whole-trace equality, or finite-stage membership of the original projections is assumed. Constant positive finite-matrix systems are included. An empty matrix stage cannot support the nonzero localized inputs. In a trivial algebra the nonzero-input hypotheses are impossible.")),
                    Paragraph(Text("This is the intrinsic unital-algebra supplier used by the existing full-PB source. A Lean realization of the actual ambient corner C = PAP is a separate bridge. The supplier alone does not establish the scalar remainder classification, response equality, or the original full PB endpoints."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula D(long n) => new Formula.Number(n);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Star(Formula a) => Call("star", a);
    private static Formula Proj(Formula a) => Call("IsStarProjection", a);
    private static Formula Conj(Formula u, Formula p) => Multiply(Multiply(u, p), Star(u));
    private static Formula Stage(Formula n) => Call("Fin", Call("size", X("M"), n));
    private static Formula Mat(Formula n) => Call("Matrix", Stage(n), Stage(n), Call("Complex"));
    private static Formula Arrow(Formula a, Formula b) => F.Seq(Par(a), F.To, Par(b));
    private static Formula Alg(Formula body) => All("C", Call("Type"),
        F.Seq(F.OpenBracket, Call("CStarAlgebra", X("C")), F.CloseBracket, F.Sp,
            All("M", Call("FullMatrixModel", X("C")), body)));
    private static Formula InSet(string name, Formula body) => All(name, Stage(X("N")), Imp(Mem(X(name), X("s")), body));
    private static Formula Conjunct(params Formula[] terms)
    {
        Formula result = terms[^1];
        for (int i = terms.Length - 2; i >= 0; --i) result = And(terms[i], result);
        return result;
    }
    private static Formula Localization()
    {
        Formula result = And(Proj(X("Q")),
            Equal(Conj(X("u"), X("p")), Call("embed", X("M"), X("n"), X("Q"))));
        result = Ex("Q", Mat(X("n")), result);
        result = Ex("u", Call("unitary", X("C")), result);
        result = Ex("n", Call("Nat"), result);
        return Alg(All("p", X("C"), Imp(Proj(X("p")), result)));
    }
    private static Formula Matching()
    {
        Formula li = App(X("l"), X("i"));
        Formula lj = App(X("l"), X("j"));
        Formula wi = App(X("w"), X("i"));
        Formula orth = InSet("i", InSet("j", Imp(Ne(X("i"), X("j")), Equal(Multiply(li, lj), D(0)))));
        Formula sum = F.Seq(new Formula.Subscript(F.Sum, F.Seq(X("i"), F.InMacro, F.Sp, X("s"))), Par(li));
        Formula law = Conjunct(Call("Nonempty", X("s")),
            InSet("i", And(Proj(li), Ne(li, D(0)))), orth, Equal(sum, X("r")),
            Proj(X("m")), Ne(X("m"), D(0)),
            Equal(Multiply(X("m"), X("v")), X("m")),
            Equal(Multiply(X("v"), X("m")), X("m")),
            InSet("i", And(Equal(Multiply(Star(wi), wi), X("m")),
                Equal(Multiply(wi, Star(wi)), li))));
        Formula conclusion = Ex("N", Call("Nat"), Ex("s", Call("Finset", Stage(X("N"))),
            Ex("l", Arrow(Stage(X("N")), X("C")), Ex("m", X("C"),
                Ex("w", Arrow(Stage(X("N")), X("C")), law)))));
        return Alg(All("r", X("C"), All("v", X("C"), Imp(Proj(X("r")), Imp(Proj(X("v")),
            Imp(Ne(X("r"), D(0)), Imp(Ne(X("v"), D(0)), conclusion)))))));
    }
}
