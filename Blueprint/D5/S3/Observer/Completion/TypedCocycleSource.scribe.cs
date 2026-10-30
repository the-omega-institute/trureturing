using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;
internal sealed class TypedCocycleSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire actual shared-name two-loop source and its ordered histories.",
        H("Typed two-loop source correspondence"),
        Blocks(Describe.Lean(DescribeId.Create("typed-cocycle-source-correspondence"),
            DeclarationHandle.Create("D5/S3/Observer/Completion/TypedCocycleSource.source_correspondence"),
            H("Exhaustive legal words and native totals"), StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("There is one type, vertices p, s, t, and exactly the transitions p-a-p, p-c-s, s-a-s, s-e-t. The two loop edges have the identical operation name a. All other transitions reject and t is terminal. The complete response retains current readouts, ordered success records with name, successor and edge vector, and the first illegal attempt. The theorem proves that equality of every complete continuation response is exactly equality of states: the empty response separates distinct vertices and deterministic execution supplies identical later responses from equal vertices. No reset, failure, archive or Stop operation is added.")),
                Paragraph(Text("History.pre m, History.mid m n and History.terminal m n represent exactly a^m, a^m c a^n and a^m c a^n e, for arbitrary natural counts. The theorem proves injectivity of the ordered word map and equivalence between execution of any finite root word and existence of its normal form. Therefore every finite cut, the empty word, c, ce, zero counts and terminal histories are included.")),
                Paragraph(Text("The accumulator follows the four source edges. At p the a vector is (h,h); at s it is (h,2h); the c and e vectors are the fixed C and E. The theorem derives the normal-form totals from this accumulator: (hm,hm), C+h(m+n,m+2n), and C+E+h(m+n,m+2n). Offsets are allowed to be arbitrary real pairs; positive h,C,E give the specified native source.")),
                Paragraph(Text("This is a mathematical model with fixed native vectors and exact named execution. It supplies no physical calibration or acquisition of the source state. The proof uses induction on execution and the unique separating c position; the sharp-cost theorem consumes its injectivity bridge to recover original ordered words."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula All(Formula variables, Formula type, Formula body) =>
        Seq(Forall, Sp, variables, Colon, Sp, type, Comma, Sp, body);

    private static Formula Same(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);

    private static Formula Both(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);

    private static Formula TheoremFormula()
    {
        Formula h = F.Id("h"), c = F.Id("C"), e = F.Id("E");
        Formula w = F.Id("w"), z = F.Id("z"), u = F.Id("u");
        Formula x = F.Id("x"), y = F.Id("y");
        Formula history = Call("History"), vertex = Call("Vertex");
        Formula word = Call("word", u), endpoint = Call("endpoint", u);
        Formula p = Seq(Operatorname, Grp(F.Id("p")));
        Formula legal = All(w, Call("List", Call("Name")), All(z, vertex,
            Seq(Call("execute", p, w), Sp, Eq, Sp, Call("some", z), Sp, Iff, Sp,
                Exists, Sp, u, Colon, Sp, history, Comma, Sp,
                Both(Same(word, w), Same(endpoint, z)))));
        Formula totals = All(u, history, Both(
            Same(Call("execute", p, word), Call("some", endpoint)),
            Same(Call("accumulate", h, c, e, p, word),
                Call("some", Call("native", h, c, e, u)))));
        Formula responses = All(Seq(x, Comma, Sp, y), vertex,
            Seq(Call("SameResponses", h, c, e, x, y), Sp, Iff, Sp, Same(x, y)));
        return Disp(All(h, Seq(Mathbb, Grp(F.Id("R"))),
            All(Seq(c, Comma, Sp, e), Call("Vector"),
                Both(Call("Injective", Seq(Operatorname, Grp(F.Id("word")))),
                    Both(legal, Both(totals, responses))))));
    }
}
