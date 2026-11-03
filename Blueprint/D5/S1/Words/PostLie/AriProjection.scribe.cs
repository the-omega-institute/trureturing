using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.PostLie;
internal sealed class AriProjectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/PostLie/AriProjection";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/LieTheory/burmesterkuhn2025postlie");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Pure-word projection and original ari action support", H("AriProjection"), Blocks(
        Paragraph(Text("N includes zero. Word is the free monoid on N and H is the finite rational word algebra. Coefficients use the ordinary concatenation basis. All k and s are unrestricted natural indices, including zero.")),
        Entry("pureprojection-coeff", "pureProjection_coeff", "pureProjection_coeff", Ns(new[]{"k","d"},Q("p",V("H"),Equal(Call("coeff",Call("pureProjection",V("k"),V("p")),V("d")),Coeff(V("p"),Call("ofList",Call("replicate",V("d"),V("k"))))))), "The empty word is included at d=0, with no factorial normalization. Rational coefficients and cancellation are unrestricted.", DescribeRole.Theorem),
        Entry("pureprojection-commutator", "pureProjection_commutator", "pureProjection_commutator", Q("k",V("N"),Q("p",V("H"),Q("q",V("H"),Equal(Call("pureProjection",V("k"),Call("commutator",V("p"),V("q"))),Num(0))))), "An algebra homomorphism to the commutative polynomial algebra kills every ordinary commutator.", DescribeRole.Theorem),
        Entry("letteraction-projection", "letterAction_projection", "letterAction_projection", Q("k",V("N"),Q("A",V("Word"),Q("s",V("N"),Imp(NotEqual(V("A"),Num(1)),Equal(Call("pureProjection",V("k"),LA(V("A"),V("s"))),Num(0)))))), "A nonempty left word produces nested commutators for positive s and zero for s=0. Both project to zero.", DescribeRole.Theorem),
        Entry("letteraction-above", "letterAction_above", "letterAction_above", Q("k",V("N"),Q("A",V("Word"),Q("s",V("N"),Mem(LA(V("A"),V("s")),Call("above",V("k"),Call("level",V("k"),Call("of",V("s")))))))), "The empty-left-word branch is the generator itself. In every other branch the projection identity excludes all pure words, so s different from k contributes at least one non-k letter.", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string s) => F.Id(s);
    private static Formula Q(string x, Formula t, Formula b) => Seq(Forall,Sp,V(x),Colon,t,Comma,b);
    private static Formula Ns(string[] xs, Formula b) { for (var i=xs.Length-1;i>=0;i--) b=Q(xs[i],V("N"),b); return b; }
    private static Formula Imp(Formula a, Formula b) => Seq(Open,a,Close,Sp,Implies,Sp,b);
    private static Formula Mem(Formula a, Formula b) => Seq(a,Sp,InMacro,Sp,b);
    private static Formula Coeff(Formula p, Formula w) => Call("coeff",p,w);
    private static Formula LA(Formula a, Formula s) => Call("letterAction",a,s);
}
