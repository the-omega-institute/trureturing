using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class ColumnSynthesisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-summable columns on an arbitrary complete complex Hilbert space.",
        H("Hilbert-Schmidt column synthesis"), Blocks(Describe.Lean(
            DescribeId.Create("hilbert-schmidt-column-synthesis"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis.exists_hilbertSchmidt_of_square_summable_columns"),
            H("Synthesis and operator norm"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")), Blocks(
                Paragraph(Text("Let b be any Hilbert basis of a complete complex Hilbert space H, indexed by a set w of H. For any columns v with summable real squared norms, the series A x equals the sum of inner(b_i,x) times v_i converges absolutely. Parseval and the attributed scalar Cauchy-Schwarz estimate bound its norm uniformly by the square root of the column square sum times norm(x). The series defines a continuous linear map with exactly the prescribed columns. Its Hilbert-Schmidt square sum is exactly that of v, and its operator norm satisfies the displayed bound.")),
                Paragraph(Text("The construction allows uncountable basis indices, arbitrary zero columns and the zero space. It is used both for the weighted inverse-square-root extension and for the residual of each finite column approximation. Equality with an existing continuous operator follows from equality on the basis and density of its linear span.")),
                Paragraph(Text("The square-sum product and summability suppliers are Tom Ole Diem's Physlib proofs at revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0, as documented in the analytic trace-supplier Library note. The synthesis construction is a repository derivation; no mathematical originality is claimed for the supplied scalar estimates."))), DescribeRole.Theorem))));
    private static Formula Endpoint()
    {
        Formula h = F.Id("H"), w = F.Id("w"), b = F.Id("b"), v = F.Id("v"), a = F.Id("A"), i = F.Id("i");
        Formula vi = new Formula.Apply(v, [i]), bi = new Formula.Apply(b, [i]);
        Formula ai = new Formula.Apply(a, [bi]);
        Formula vs = Call("tsum", Seq(Call("square", Call("norm", vi)), i, w));
        Formula asum = Call("tsum", Seq(Call("square", Call("norm", ai)), i, w));
        Formula body = Conj(All([new(FormulaIdentifier.Create("i"), w)], Equal(ai, vi)),
            Conj(Call("IsHilbertSchmidt", a), Conj(Equal(asum, vs), Le(Call("norm", a), Call("sqrt", vs)))));
        return All([new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
            new(FormulaIdentifier.Create("w"), Call("Set", h)),
            new(FormulaIdentifier.Create("b"), Call("HilbertBasis", w, h)),
            new(FormulaIdentifier.Create("v"), Call("Function", w, h))],
            Imp(Call("Summable", Seq(Call("square", Call("norm", vi)), i, w)),
                new Formula.BindMany(FormulaQuantifier.Exists,
                    [new(FormulaIdentifier.Create("A"), Call("BoundedComplexOperator", h))], body)));
    }
    private static Formula Conj(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
