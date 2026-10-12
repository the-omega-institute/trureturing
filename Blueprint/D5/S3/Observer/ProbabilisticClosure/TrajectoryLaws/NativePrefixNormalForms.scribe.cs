using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativePrefixNormalFormsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePrefixNormalForms.";

    public DocumentDefinition Create()
    {
        Formula nf = F.Id("nf"), ng = F.Id("ng"), op = F.Id("op");
        Formula form = F.Id("PrefixForm");
        Formula unique = Call("Injective", F.Id("render"));
        Formula extension = All("nf", form, All("ng", form, All("op", F.Id("Operation"),
            Imp(Equal(Call("appendForm", nf, op), Call("some", ng)),
                Equal(Call("render", ng), Call("append", Call("render", nf), Call("singleton", op)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Unique independently concatenated forms for all paid native prefix cuts.",
            H("Ordered retries and partial payload words"), Blocks(
                Paragraph(Text("A PrefixForm contains an arbitrary ordered list u of rejected equal pairs. retryWord replaces each bit x in u by [x,x]. The tail is seed-ready, one pending first seed letter, or an acquired seed rho followed by PayloadForm with four remaining slots. The accepted seed word is [0,1] for rho=0 and [1,0] for rho=1. These concatenations define render independently of native execution.")),
                Paragraph(Text("With positive remaining slots, PayloadForm is an active cut after j beta-alpha returns, with phase p or one pending beta, or a completed pWord(j,b) followed by a form with one fewer slot. With no slots it is pending or delivered. Pending renders empty; delivered renders exactly Stop of the last completed bit. Every j is a natural number. Thus empty and partial seed histories, every payload cut, both final colors and the original delivery boundary are represented.")),
                Node("prefix-form-unique", "prefix_form_unique", "The complete concatenation is injective", unique,
                    "parseSeed scans actual equal-pair retry order and the first unequal pair. parsePayload independently decodes concatenated segment words and active suffixes. Induction proves that parsing each rendered form returns that same form, including all natural return counts and terminal cuts. Therefore equal rendered operation words have equal forms. This decoder does not define native legality or store any archive in native state."),
                Node("render-append-form", "render_append_form", "Right extension preserves concatenation", extension,
                    "appendForm extends the proof form by one original Read or Stop. A same-letter second seed Read appends that rejection to u; an unequal second Read acquires its seed. Payload beta-alpha adds a return, while a completing letter adds a segment and its fresh successor. Only a pending matching Stop extends to delivered. Whenever extension succeeds with ng, render(ng) is render(nf) followed by precisely op. Induction follows the independent payload grammar."))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(x), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Open, premise, Close, Rightarrow, Open, body, Close);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
