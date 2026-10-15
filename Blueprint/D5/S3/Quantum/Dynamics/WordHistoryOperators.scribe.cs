using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class WordHistoryOperatorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Creation on all finite words and the unbounded length multiplier on finite support.",
        H("Word history operators"),
        Blocks(Describe.Lean(DescribeId.Create("number-unbounded"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/WordHistoryOperators.number_unbounded"),
            H("No bounded extension of word length multiplication"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/arias1994fock")),
            Blocks(
                Paragraph(Text("Let Alphabet be any type and g one of its letters. WordHilbert is the complex Hilbert space ell2 of all finite lists over Alphabet, including the empty word and arbitrarily long words. FiniteSupport means that only finitely many word coordinates are nonzero. The number operator multiplies each word coordinate by its length; its finite-support argument proves that the resulting vector still belongs to ell2. For any proposed continuous linear extension A, choose an integer n larger than its operator norm. The unit basis vector at the word replicate n g has number-operator norm n, contradicting the operator-norm bound for A. This is an arbitrary-alphabet operator obstruction, not a finite truncation or a claim of a bounded length operator.")),
                Paragraph(Text("The right append map is defined canonically from the orthogonal family of coordinate lines at words ending in g. OrthogonalFamily.linearIsometry supplies its extension to the complete Hilbert space and preserves its norm. Its single-coordinate rule, lp.evalCLM and map_tsum give the coordinate at wg and zero outside that image. Applying the adjoint inner-product identity to a basis vector gives the adjoint coordinate at wg. Thus LinearIsometry.adjoint_comp_self gives Sg* Sg=I, while Sg Sg* is the projection onto words ending in g. Evaluation at the empty-word unit vector shows the projection is proper.")),
                Paragraph(Text("Finite partial sums of lp.hasSum_single prove density of finite support. The support of Nf is contained in the support of f; creation sends the support into the append image; the adjoint sends it into the dropLast image. These are a common invariant dense domain. On that domain the coordinate length identity length(wg)=length(w)+1 gives NSg-SgN=Sg. Appending any inverse-readout letter is still creation: its action on the empty-word vector differs from Sg*, and two appends send the basis word w to the longer word wg inverse, never back to w. These exact applications of orthogonal-family, adjoint, summation and list identities remain temporary compiled applications rather than additional named project theorems. Their definitions, parameter correspondence and derivation are retained here.")),
                Paragraph(Text("The original finite nonempty alphabet supplies g, so it is a special case without a bound on word length. A readout that assigns inverse system gates does not impose cancellation on the free word carrier. Arias and Popescu use left creation on Fock space; word reversal identifies that convention with this right append convention. The theorem is reusable formal content; no claim of new literature mathematics is made."))),
            DescribeRole.Theorem))));

    private static Formula Presentation()
    {
        Formula alphabet = F.Id("Alphabet");
        Formula space = Call("WordHilbert", alphabet);
        Formula equality = Rel(Call("apply", F.Id("A"), F.Id("f")), Eq,
            Call("number", F.Id("f"), F.Id("hf")));
        Formula domain = All("f", space,
            All("hf", Call("FiniteSupport", F.Id("f")), equality));
        Formula obstruction = Seq(Neg,
            Ex("A", Call("ContinuousComplexLinearMap", space, space), domain));
        return Disp(All("Alphabet", Call("Type"), All("g", alphabet, obstruction)));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
}
